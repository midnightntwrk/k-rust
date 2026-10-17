//! The backend reads a predicate only from predicate-shaped patterns.
//!
//! A K condition is emitted as `\equals{Bool, R}(P, true)`: the Boolean term `P = true`, or, when
//! `P` is a matching-logic connective at the condition's root, the encoding of "`P` holds". Below
//! that root, the operands of `#Equals` (and of `#Ceil`, `#Floor`, `#In`) are term positions,
//! where a connective denotes a set of values (`(X ==Int 1) #And (X ==Int 2)` is the intersection
//! of two singletons), which no predicate the backend reads states. A definition with such an
//! operand, or with a connective over terms of another sort than Bool at a matched position
//! (`3 #Implies 4` of sort Int), is refused when it loads, naming the axiom, instead of being read
//! with a meaning it does not have. These tests drive the library route a client of the
//! compiler uses: load the K source with the prelude, compile it, and load the KORE.

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, HaltReasonOutput, ProveRequest,
        ResultModalityOutput, UnstatedDefinedness,
    },
    builtin::embedded,
    definition::CheckMode,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{codec, parser::parse_definition, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
};
use k_rust_backend::definition::{BackendDefinition, DefinitionError};

const MAIN: &str = "MLP";
const FILE: &str = "mlp.k";
/// The line of `mlp.k` on which [`source`] writes the rule under test.
const RULE_LINE: usize = 22;

/// A definition whose rule under test, `rule`, is written on line [`RULE_LINE`] of `mlp.k`, and
/// whose `extra` sentences follow it.
fn source(rule: &str, extra: &str) -> String {
    format!(
        "module MLP-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
               | run(Int) [symbol(run)]
               | pair(Int, Step) [symbol(pair)]
               | test(Bool) [symbol(test)]
  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]
endmodule

module MLP
  imports MLP-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(Int) [symbol(done)]
  syntax Int ::= f(Int) [function, symbol(f)]
  syntax Bool ::= oneOrTwo(Int) [macro]
  rule oneOrTwo(X) => (X ==Int 1) #Or (X ==Int 2)
  rule <k> run(X) => done(f(X)) ... </k>
  // the rule under test is on the next line
  {rule}
  {extra}
endmodule
"
    )
}

/// The compiled KORE of `source`, which must compile.
fn compile(source: &str) -> String {
    compile_with(source, MAIN, CompileOptions::default())
}

/// The compiled KORE of `source` with main module `main`, which must compile under `options`.
fn compile_with(source: &str, main: &str, options: CompileOptions) -> String {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new(FILE, source),
        main,
        Some("MLP-SYNTAX"),
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").expect("the embedded prelude exists")],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("the definition loads: {error:?}\n{source}"));
    compile_loaded_definition(&loaded, options)
        .unwrap_or_else(|error| panic!("the definition compiles: {error:?}\n{source}"))
        .definition_kore
}

/// The error with which the backend refuses `kore`, or the leaves of `go(1)` when it loads it.
fn refusal(kore: &str) -> DefinitionError {
    let syntax = parse_definition(kore).expect("compiled KORE parses");
    match BackendDefinition::internalize(&syntax, MAIN) {
        Err(error) => error,
        Ok(_) => {
            let mut backend =
                Backend::new(kore, MAIN, BackendOptions::default()).expect("the definition loads");
            panic!(
                "the definition loads; go(1) gives {:?}, run(1) gives {:?}, pair(3, sa) gives {:?}, \
                 test(true) gives {:?}, test(false) gives {:?}",
                leaves(&mut backend, "go", 1),
                leaves(&mut backend, "run", 1),
                leaves(&mut backend, "pair", 3),
                leaves(&mut backend, "test", 1),
                leaves(&mut backend, "test", 0),
            )
        }
    }
}

/// The program `head(argument)` (`pair(argument, sa)` for `pair`, `test(argument != 0)` for
/// `test`), as a configuration.
fn configuration(head: &str, argument: i64) -> String {
    let int = format!("\\dv{{SortInt{{}}}}(\"{argument}\")");
    let program = match head {
        "pair" => format!("Lblpair{{}}({int}, Lblsa{{}}())"),
        "test" => format!("Lbltest{{}}(\\dv{{SortBool{{}}}}(\"{}\"))", argument != 0),
        head => format!("Lbl{head}{{}}({int})"),
    };
    format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, \
         SortKItem{{}}}}({program}), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}(\\dv{{SortInt{{}}}}(\"0\")))"
    )
}

/// The halt reason and compact state of each leaf of running `head(argument)`.
fn leaves(backend: &mut Backend, head: &str, argument: i64) -> Vec<(HaltReasonOutput, String)> {
    let state = parse_pattern(&configuration(head, argument)).unwrap();
    backend
        .execute(ExecuteRequest {
            result_modality: ResultModalityOutput::PathSet,
            max_depth: Some(4),
            ..ExecuteRequest::new(state)
        })
        .unwrap()
        .leaves
        .into_iter()
        .map(|leaf| {
            (
                leaf.reason,
                Printer::compact().print_pattern(&codec::from_value(&leaf.state).unwrap()),
            )
        })
        .collect()
}

/// Whether the leaves of a run are one `Stuck` leaf whose `<k>` cell starts with `expected` (the
/// KORE of its first item, such as `Lbldone{}(\dv{SortInt{}}("1"))`).
fn runs_to(leaves: &[(HaltReasonOutput, String)], expected: &str) -> bool {
    matches!(
        leaves,
        [(HaltReasonOutput::Stuck, state)] if state.contains(&format!("kseq{{}}({expected}"))
            || state.contains(&format!("kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}({expected}"))
    )
}

fn done(value: i64) -> String {
    format!("Lbldone{{}}(\\dv{{SortInt{{}}}}(\"{value}\"))")
}

fn go(value: i64) -> String {
    format!("Lblgo{{}}(\\dv{{SortInt{{}}}}(\"{value}\"))")
}

/// Whether `error` is the variant whose debug form starts with `variant`. The variants are
/// matched by name so that this file also builds against a backend that lacks them, where each
/// refusal it expects fails as a definition that loads.
fn is(error: &DefinitionError, variant: &str) -> bool {
    format!("{error:?}").starts_with(variant)
}

/// The error names the rule by its label and the line it is written on.
fn assert_names_the_rule(error: &DefinitionError) {
    let text = error.to_string();
    assert!(text.contains("MLP.p"), "{text}");
    assert!(text.contains(&format!("{FILE}:{RULE_LINE}:")), "{text}");
}

/// The conditions whose `#Equals` has an operand that is a matching-logic connective over terms.
const CONNECTIVE_OPERANDS: &[&str] = &[
    "{((X ==Int 1) #And (X ==Int 2)) #Equals false}",
    "{true #Equals ((X ==Int 1) #Or (X ==Int 2))}",
    "{((X ==Int 1) #Or (X ==Int 2)) #Equals true}",
    "{X #Equals (1 #Or 2)}",
];

fn assert_reads_term_as_predicate(rule: &str) {
    let kore = compile(&source(rule, ""));
    let error = refusal(&kore);
    assert!(is(&error, "AxiomReadsTermAsPredicate"), "{rule}: {error:?}");
    assert_names_the_rule(&error);
    assert!(
        error
            .to_string()
            .contains("whose operand is a matching-logic connective over terms"),
        "{error}"
    );
    let facade = Backend::new(&kore, MAIN, BackendOptions::default())
        .err()
        .expect("the facade refuses the definition");
    assert!(facade.message().contains("MLP.p"), "{facade}");
}

#[test]
fn a_rewrite_rule_whose_equality_has_a_connective_operand_is_refused_at_load() {
    for condition in CONNECTIVE_OPERANDS {
        assert_reads_term_as_predicate(&format!(
            "rule [p]: <k> go(X) => done(X) ... </k> requires {condition}"
        ));
    }
}

#[test]
fn a_function_equation_whose_equality_has_a_connective_operand_is_refused_at_load() {
    for condition in CONNECTIVE_OPERANDS {
        assert_reads_term_as_predicate(&format!("rule [p]: f(X) => X requires {condition}"));
    }
}

/// A condition conjoined to a matched term (`t #And {P}`) is no condition root: its `#Equals`
/// is read as written wherever it sits, so a connective in its operand is refused as in a
/// `requires`. `{true #Equals (B #Or false)}` states `{true} = {B, false}`, and
/// `{(B #And true) #Equals false}` states `{B} ∩ {true} = {false}`: neither holds for any `B`.
#[test]
fn a_matched_condition_whose_equality_has_a_connective_operand_is_refused_at_load() {
    for condition in [
        "{true #Equals (B #Or false)}",
        "{(B #And true) #Equals false}",
    ] {
        assert_reads_term_as_predicate(&format!(
            "rule [p]: <k> test(B #And {condition}) => done(0) ... </k>"
        ));
    }
}

/// A connective over Int terms under a term-level `\and` at a matched or shared position is no
/// predicate: `3 #Implies 4` of sort Int is the set `(Int ∖ {3}) ∪ {4}`.
#[test]
fn a_connective_over_terms_at_a_matched_position_is_refused_at_load() {
    for rule in [
        "rule [p]: <k> pair(3 #Implies 4, (sa => sb)) ... </k>",
        "rule [p]: <k> go(X #And (3 #Implies 4)) => done(X) ... </k>",
    ] {
        let error = refusal(&compile(&source(rule, "")));
        assert!(
            is(&error, "RulePattern(TermConnectiveInConjunction")
                || is(&error, "RulePattern(NonBoolTermAsPredicate"),
            "{rule}: {error:?}"
        );
        let text = error.to_string();
        assert!(text.contains("implies"), "{text}");
        assert!(text.contains("module MLP"), "{text}");
    }
}

/// `#Not` under the same `\and` keeps its own refusal.
#[test]
fn a_negated_configuration_at_a_shared_position_keeps_its_refusal() {
    let error = refusal(&compile(&source(
        "rule [p]: <k> pair(#Not(3), (sa => sb)) ... </k>",
        "",
    )));
    assert!(is(&error, "RulePattern(NegatedConfiguration"), "{error:?}");
    assert!(
        error.to_string().contains("negates (\\not) a pattern"),
        "{error}"
    );
}

/// A rule under test, the sentences beside it, and the programs `go(n)` with what each runs to.
type Case = (String, &'static str, Vec<(i64, String)>);

/// Conditions whose atoms are predicates over terms, and connectives at a condition's root, are
/// read as written: each loads and runs each program to the configuration its meaning gives.
#[test]
fn predicate_conditions_load_and_answer_as_written() {
    let go_rule =
        |condition: &str| format!("rule [p]: <k> go(X) => done(X) ... </k> requires {condition}");
    let one_or_two = [(1, done(1)), (2, done(2)), (3, go(3))];
    let cases: Vec<Case> = vec![
        (go_rule("{X #Equals 1}"), "", vec![(1, done(1)), (3, go(3))]),
        (
            go_rule("#Ceil(1 /Int X)"),
            "",
            vec![(1, done(1)), (0, go(0))],
        ),
        (
            go_rule("#Exists Y . {X #Equals Y +Int 1}"),
            "",
            vec![(1, done(1))],
        ),
        (
            go_rule("(X ==Int 1) #Or (X ==Int 2)"),
            "",
            one_or_two.to_vec(),
        ),
        (go_rule("oneOrTwo(X)"), "", one_or_two.to_vec()),
        (
            "rule [p]: <k> go(X #And (1 #Or 2)) => done(X) ... </k>".to_owned(),
            "",
            one_or_two.to_vec(),
        ),
        (
            "rule [p]: <k> go(X #And {X #Equals 1}) => done(X) ... </k>".to_owned(),
            "",
            vec![(1, done(1)), (3, go(3))],
        ),
        // The `owise` rule's competitor has a predicate condition, which the priority reads.
        (
            go_rule("{X #Equals 1}"),
            "rule <k> go(_) => done(0) ... </k> [owise]",
            vec![(1, done(1)), (3, done(0))],
        ),
    ];
    // Without a solver, the existential and the disjunction the compiler aliases (`#Or` with a
    // fresh variable `?_Gen0` conjoined to it) are not decided for the subjects that satisfy
    // them; that incompleteness is not this file's.
    let undecided_without_a_solver = |rule: &str| {
        !cfg!(feature = "z3-inference") && (rule.contains("#Exists") || rule.contains(") #Or ("))
    };
    let mut wrong = Vec::new();
    for (rule, extra, runs) in &cases {
        let kore = compile(&source(rule, extra));
        let mut backend = Backend::new(&kore, MAIN, BackendOptions::default())
            .unwrap_or_else(|error| panic!("{rule} loads: {error}"));
        for (argument, expected) in runs {
            let leaves = leaves(&mut backend, "go", *argument);
            let undecided = matches!(&leaves[..], [(HaltReasonOutput::Indeterminate, _)]);
            let satisfied = !expected.starts_with("Lblgo");
            if !(runs_to(&leaves, expected)
                || (undecided && satisfied && undecided_without_a_solver(rule)))
            {
                wrong.push(format!("{rule} {extra}: go({argument}) gives {leaves:?}"));
            }
        }
    }
    assert!(wrong.is_empty(), "{wrong:#?}");
}

/// The KORE of `claims`, a module `MLP-SPEC` over [`source`] with a rule `go(X) => done(X)`,
/// compiled for proving as `kprove` compiles it.
fn spec(claims: &str) -> String {
    let spec = format!(
        "{}
module MLP-SPEC
  imports MLP
{claims}
endmodule
",
        source("rule [p]: <k> go(X) => done(X) ... </k>", "")
    );
    compile_with(
        &spec,
        "MLP-SPEC",
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: MAIN.to_owned(),
            },
            ..CompileOptions::default()
        },
    )
}

/// A claim's condition is compiled as the definition's are: a connective inside an operand of
/// its `#Equals` is not the encoding of a condition, wherever the equality sits, so the claim is
/// refused as one whose constraints cannot be read faithfully; a connective at the condition's
/// root is the encoding, and is read.
#[test]
fn a_claim_whose_equality_has_a_connective_operand_is_refused() {
    let kore = spec(
        "  claim [q]: <k> go(X) => done(X) ... </k> requires {true #Equals ((X ==Int 1) #Or (X ==Int 2))}
  claim [s]: <k> go(X) => done(X) ... </k> requires (X ==Int 1) #Or (X ==Int 2)",
    );
    let mut backend = Backend::new(&kore, "MLP-SPEC", BackendOptions::default())
        .unwrap_or_else(|error| panic!("the spec loads: {error}"));
    let refused = backend
        .prove(ProveRequest {
            claim: Some("MLP-SPEC.q".into()),
            max_depth: Some(4),
            ..ProveRequest::default()
        })
        .map(|result| result.status)
        .expect_err("the claim is refused");
    assert_eq!(
        refused.claim_refusal(),
        Some(&UnstatedDefinedness::TermReadAsPredicate),
        "{refused}"
    );
    let read = backend.prove(ProveRequest {
        claim: Some("MLP-SPEC.s".into()),
        max_depth: Some(4),
        ..ProveRequest::default()
    });
    assert!(
        read.as_ref()
            .map_or_else(|error| error.claim_refusal().is_none(), |_| true),
        "{:?}",
        read.map(|result| result.status)
    );
}

/// A claim that reads an Int term as a predicate (`{X #Equals (1 #Or 2)}`, whose operand
/// `1 #Or 2` would be read as `1 = true \/ 2 = true`) is refused when the spec loads, as a
/// definition axiom with one is, since such a term has no reading as a predicate at all.
#[test]
fn a_claim_that_reads_an_int_term_as_a_predicate_is_refused_at_load() {
    let kore = spec("  claim [r]: <k> go(X) => done(X) ... </k> requires {X #Equals (1 #Or 2)}");
    let error = Backend::new(&kore, "MLP-SPEC", BackendOptions::default())
        .err()
        .expect("the spec is refused");
    assert!(
        error
            .message()
            .contains("a term of sort SortInt{} is read as a predicate"),
        "{error}"
    );
}
