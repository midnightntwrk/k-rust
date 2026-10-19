//! A condition is emitted as the predicate it states: the matching-logic connectives at its root
//! are predicate connectives at the sentence's sort, the atoms `#Equals`, `#Ceil`, `#Floor` and
//! `#In` keep their operand sort and take the sentence's sort, and each Bool term directly below
//! that spine is the predicate `\equals{SortBool{}, R}(t, \dv{SortBool{}}("true"))`. A plain Bool
//! condition is one such leaf, so its KORE is the leaf alone. The LLVM target keeps the Bool-term
//! form, which is what its interpreter evaluates.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ProveRequest},
    builtin::embedded,
    definition::{
        Attributes, CheckMode, LOCATION_ATTRIBUTE, ResolvedDefinition, SOURCE_ATTRIBUTE, Sentence,
    },
    inner::definition_with_named_projections,
    kast::Term,
    kompile::{
        CompilationBackend, CompileOptions, CompileSearchPatternError, CompiledKoreArtifacts,
        compile_loaded_definition, compile_search_pattern,
    },
    kore::{ast::Pattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_for_compilation, load_with_options},
    provenance::{GeneratingPass, ProvenanceLink},
};

const HEADER: &str = "module P-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(Int) [symbol(done)]
";

const F: &str = "  syntax Int ::= f(Int) [function, symbol(f)]\n";
const G: &str = "  rule [g]: <k> go(X) => done(f(X)) ... </k>\n";

const TRUE: &str = "\\dv{SortBool{}}(\"true\")";
const TOP: &str = "SortGeneratedTopCell{}";

fn compile_for(sentences: &str, backend: CompilationBackend) -> String {
    compile_artifacts(sentences, backend).definition_kore
}

fn compile_artifacts(sentences: &str, backend: CompilationBackend) -> CompiledKoreArtifacts {
    compile_source(format!("{HEADER}{sentences}endmodule\n"), backend)
}

/// The whole definition `source`, main module `P` and syntax module `P-SYNTAX`, compiled.
fn compile_source(source: String, backend: CompilationBackend) -> CompiledKoreArtifacts {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![
            embedded("kast.md").unwrap(),
            embedded("prelude.md").unwrap(),
        ],
        ..backend.load_options()
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("ml_conditions.k", source),
        "P",
        Some("P-SYNTAX"),
        &mut resolver,
        &options,
    )
    .expect("the definition loads");
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
    .expect("the definition compiles")
}

fn compile(sentences: &str) -> String {
    compile_for(sentences, CompilationBackend::Rust)
}

/// The axiom or claim labelled `label`, whitespace collapsed.
fn axiom(kore: &str, label: &str) -> String {
    let needle = format!("label{{}}(\"{label}\")");
    let at = kore
        .find(&needle)
        .unwrap_or_else(|| panic!("no axiom labelled {label}"));
    let start = ["axiom{", "claim{"]
        .into_iter()
        .filter_map(|keyword| kore[..at].rfind(keyword))
        .max()
        .expect("an axiom or a claim precedes its label");
    let end = at + kore[at..].find(']').expect("the attribute list closes");
    kore[start..=end]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace("( ", "(")
        .replace(" )", ")")
}

fn int(value: &str) -> String {
    format!("\\dv{{SortInt{{}}}}(\"{value}\")")
}

/// `\equals{SortBool{}, sort}(term, true)`: a Bool term read as a predicate.
fn leaf(sort: &str, term: &str) -> String {
    format!("\\equals{{SortBool{{}}, {sort}}}({term}, {TRUE})")
}

const X: &str = "VarX:SortInt{}";

fn x_equals(sort: &str, value: &str) -> String {
    format!("\\equals{{SortInt{{}}, {sort}}}({X}, {})", int(value))
}

fn eq_int(left: &str, right: &str) -> String {
    format!("Lbl'UndsEqlsEqls'Int'Unds'{{}}({left}, {right})")
}

#[track_caller]
fn assert_contains(axiom: &str, expected: &str) {
    assert!(
        axiom.contains(expected),
        "expected\n  {expected}\nin\n  {axiom}"
    );
}

#[track_caller]
fn assert_lacks(axiom: &str, unexpected: &str) {
    assert!(
        !axiom.contains(unexpected),
        "unexpected\n  {unexpected}\nin\n  {axiom}"
    );
}

/// No Bool-sorted matching-logic connective or atom: none of them is a Bool term.
#[track_caller]
fn assert_no_bool_connective(axiom: &str) {
    for connective in [
        "\\or{SortBool{}}",
        "\\and{SortBool{}}",
        "\\not{SortBool{}}",
        "\\implies{SortBool{}}",
        "\\exists{SortBool{}}",
        "\\forall{SortBool{}}",
        "\\top{SortBool{}}",
        "\\bottom{SortBool{}}",
        ", SortBool{}}(",
    ] {
        assert_lacks(axiom, connective);
    }
}

#[test]
fn an_equality_condition_is_an_equality_at_the_rule_sort() {
    let kore = compile("  rule [p]: <k> go(X) => done(X) ... </k> requires {X #Equals 1}\n");
    let axiom = axiom(&kore, "P.p");
    assert_contains(&axiom, &x_equals(TOP, "1"));
    assert_lacks(&axiom, TRUE);
}

#[test]
fn a_definedness_condition_of_an_equation_is_a_ceil_at_the_predicate_sort() {
    let kore = compile(&format!(
        "{F}  rule [p]: f(X) => X requires #Ceil(1 /Int X)\n{G}"
    ));
    let axiom = axiom(&kore, "P.p");
    assert_contains(&axiom, "\\ceil{SortInt{}, R}(");
    assert_lacks(&axiom, TRUE);
}

#[test]
fn a_disjunction_of_a_bool_term_and_a_predicate_is_a_predicate_disjunction() {
    let kore = compile(
        "  rule [p]: <k> go(X) => done(X) ... </k> requires (X ==Int 1) #Or {X #Equals 2}\n",
    );
    let axiom = axiom(&kore, "P.p");
    // The disjunction is the whole condition: no alias of it is conjoined.
    assert_lacks(&axiom, "Var'Unds'Gen");
    assert_contains(
        &axiom,
        &format!(
            "\\or{{{TOP}}}({}, {})",
            leaf(TOP, &eq_int(X, &int("1"))),
            x_equals(TOP, "2")
        ),
    );
    assert_no_bool_connective(&axiom);
}

#[test]
fn an_existential_over_a_bool_term_quantifies_its_leaf() {
    let kore = compile(
        "  rule [p]: <k> go(X) => done(X) ... </k> requires #Exists Y:Int . (X ==Int Y +Int 1)\n",
    );
    let axiom = axiom(&kore, "P.p");
    assert_contains(
        &axiom,
        &format!("\\exists{{{TOP}}}(VarY:SortInt{{}}, \\equals{{SortBool{{}}, {TOP}}}("),
    );
    assert_no_bool_connective(&axiom);
}

#[test]
fn a_negated_partial_bool_term_negates_its_leaf() {
    let kore =
        compile("  rule [p]: <k> go(X) => done(X) ... </k> requires #Not((10 /Int X) ==Int 5)\n");
    let axiom = axiom(&kore, "P.p");
    assert_contains(
        &axiom,
        &format!("\\not{{{TOP}}}(\\equals{{SortBool{{}}, {TOP}}}("),
    );
    assert_no_bool_connective(&axiom);
}

#[test]
fn plain_bool_conditions_are_one_leaf() {
    let kore =
        compile("  rule [p]: <k> go(X) => done(X) ... </k> requires X <Int 3 ensures X >Int 0\n");
    let axiom = axiom(&kore, "P.p");
    assert_contains(
        &axiom,
        &leaf(
            TOP,
            &format!("Lbl'Unds-LT-'Int'Unds'{{}}({X}, {})", int("3")),
        ),
    );
    assert_contains(
        &axiom,
        &leaf(
            TOP,
            &format!("Lbl'Unds-GT-'Int'Unds'{{}}({X}, {})", int("0")),
        ),
    );
}

#[test]
fn an_equation_ensures_is_a_predicate_at_the_equation_sort() {
    let kore = compile(&format!(
        "{F}  rule [p]: f(X) => X ensures {{X #Equals 1}}\n{G}"
    ));
    let axiom = axiom(&kore, "P.p");
    assert_contains(
        &axiom,
        &format!("\\and{{SortInt{{}}}}({X}, {})", x_equals("SortInt{}", "1")),
    );
    assert_lacks(&axiom, TRUE);
}

#[test]
fn an_owise_competitor_condition_is_its_predicate() {
    let kore = compile(&format!(
        "{F}  rule [p]: f(X) => 1 requires {{X #Equals 1}}\n  rule [o]: f(_) => 0 [owise]\n{G}"
    ));
    let axiom = axiom(&kore, "P.o");
    assert_contains(&axiom, "\\equals{SortInt{}, R}(");
    assert_lacks(&axiom, TRUE);
}

#[test]
fn the_llvm_target_keeps_the_bool_term_form() {
    let sentences = format!(
        "{F}  rule [p]: <k> go(X) => done(X) ... </k> requires {{X #Equals 1}}\n  rule [q]: f(X) => X requires #Ceil(1 /Int X) ensures {{X #Equals 1}}\n{G}"
    );
    let kore = compile_for(&sentences, CompilationBackend::Llvm);
    let rule = axiom(&kore, "P.p");
    assert_contains(
        &rule,
        &leaf(
            TOP,
            &format!("\\equals{{SortInt{{}}, SortBool{{}}}}({X}, {})", int("1")),
        ),
    );
    let equation = axiom(&kore, "P.q");
    assert_contains(
        &equation,
        "\\equals{SortBool{}, R}(\\ceil{SortInt{}, SortBool{}}(",
    );
    assert_contains(
        &equation,
        &leaf(
            "SortInt{}",
            &format!("\\equals{{SortInt{{}}, SortBool{{}}}}({X}, {})", int("1")),
        ),
    );
}

/// The compile case `exists-anon` records this axiom as a divergence from the pinned frontend
/// (`divergent-axioms` in scripts/reference-differential.toml): k-rust states the predicate.
/// The binder `_` (`_Gen0`, at the default sort K) binds only itself, so it is emitted as
/// written, binding nothing; the body's `_` (`_Gen1`) occurs in the condition alone, so it is
/// quantified existentially inside the condition.
#[test]
fn the_exists_anon_condition_is_an_existential_predicate() {
    let source = include_str!("fixtures/reference/kompile/exists-anon/test.k");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![embedded("prelude.md").unwrap()],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("exists-anon/test.k", source),
        "EXISTS-ANON",
        None,
        &mut resolver,
        &options,
    )
    .unwrap();
    let kore = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .definition_kore;
    let id = "a03b6e5bfaee958064e4c0f7a65da88eb50ef12a680f47601ad791534df4cd1b";
    let at = kore.find(id).expect("the simplification of h is emitted");
    let start = kore[..at].rfind("axiom{").unwrap();
    let axiom = kore[start..at]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace("( ", "(")
        .replace(" )", ")");
    assert!(
        axiom.starts_with(
            "axiom{R} \\implies{R}(\\exists{R}(Var'Unds'Gen1:SortInt{}, \\exists{R}(Var'Unds'Gen0:SortK{}, \\equals{SortBool{}, R}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{}, Lbl'UndsPlus'Int'Unds'{}(Var'Unds'Gen1:SortInt{}, \\dv{SortInt{}}(\"1\"))), \\dv{SortBool{}}(\"true\")))),"
        ),
        "{axiom}"
    );
}

// ---------------------------------------------------------------- partial Bool leaves

fn run(sentences: &str, n: i64) -> Vec<(String, String)> {
    run_states(sentences, n)
        .into_iter()
        .map(|(reason, k, _)| (reason, k))
        .collect()
}

/// The leaves of go(n): halt reason, the first item of `<k>`, and the whole state as KORE text.
fn run_states(sentences: &str, n: i64) -> Vec<(String, String, String)> {
    run_kore_states(&compile(sentences), n)
}

/// The leaves of go(n) of the compiled definition `kore` (see [`run_states`]).
fn run_kore_states(kore: &str, n: i64) -> Vec<(String, String, String)> {
    let mut backend = Backend::new(kore, "P", BackendOptions::default()).unwrap();
    let state = parse_pattern(&format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}(Lblgo{{}}({})), dotk{{}}())), Lbl'-LT-'generatedCounter'-GT-'{{}}({}))",
        int(&n.to_string()),
        int("0")
    ))
    .unwrap();
    let result = backend
        .execute(ExecuteRequest {
            max_depth: Some(5),
            ..ExecuteRequest::new(state)
        })
        .unwrap();
    let mut leaves: Vec<(String, String, String)> = result
        .leaves
        .iter()
        .map(|leaf| {
            let state = codec::from_value(&leaf.state).unwrap();
            (
                format!("{:?}", leaf.reason),
                k_cell(&state),
                Printer::compact().print_pattern(&state),
            )
        })
        .collect();
    leaves.sort();
    leaves
}

/// The first item of the `<k>` cell, as `go(N)`, `done(N)` or `done(f(N))`.
fn k_cell(state: &Pattern) -> String {
    fn find(pattern: &Pattern) -> Option<&Pattern> {
        match pattern {
            Pattern::Application { symbol, arguments } if symbol.name == "Lbl'-LT-'k'-GT-'" => {
                arguments.first()
            }
            Pattern::Application { arguments, .. } | Pattern::And { arguments, .. } => {
                arguments.iter().find_map(find)
            }
            _ => None,
        }
    }
    fn render(pattern: &Pattern) -> String {
        match pattern {
            Pattern::Application { symbol, arguments } => match symbol.name.as_str() {
                "kseq" | "inj" => render(&arguments[0]),
                name => {
                    let name = name.strip_prefix("Lbl").unwrap_or(name);
                    let arguments: Vec<String> = arguments.iter().map(render).collect();
                    format!("{name}({})", arguments.join(", "))
                }
            },
            Pattern::DomainValue { value, .. } => value.as_utf8().unwrap().to_owned(),
            Pattern::Variable(_) => "var".to_owned(),
            other => format!("{other:?}"),
        }
    }
    render(find(state).expect("a <k> cell"))
}

fn stuck(term: &str) -> Vec<(String, String)> {
    vec![("Stuck".to_owned(), term.to_owned())]
}

/// `#Not(t)` holds where t is undefined (t = true does not hold there); `notBool t` is undefined
/// there, so its condition does not hold. Both builds read them so, before and after the
/// faithful emission.
#[test]
fn a_negated_leaf_holds_where_its_bool_term_is_undefined() {
    let rule = |condition: &str| {
        format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n")
    };
    assert_eq!(run(&rule("#Not((10 /Int X) ==Int 5)"), 0), stuck("done(0)"));
    assert_eq!(run(&rule("#Not((10 /Int X) ==Int 5)"), 2), stuck("go(2)"));
    assert_eq!(
        run(&rule("notBool ((10 /Int X) ==Int 5)"), 0),
        stuck("go(0)")
    );

    let equation = |condition: &str| format!("{F}  rule [p]: f(X) => X requires {condition}\n{G}");
    assert_eq!(
        run(&equation("#Not((10 /Int X) ==Int 5)"), 0),
        stuck("done(0)")
    );
    let unevaluated = run(&equation("notBool ((10 /Int X) ==Int 5)"), 0);
    assert!(
        unevaluated.contains(&("Stuck".to_owned(), "done(f(0))".to_owned())),
        "f(0) stays unevaluated: {unevaluated:?}"
    );
    assert!(
        !unevaluated.iter().any(|(_, term)| term == "done(0)"),
        "{unevaluated:?}"
    );
}

// ---------------------------------------------------------------- an equality of mixed operands

/// The conditions whose spine holds an `#Equals` whose operands are not both terms and not both
/// predicates, each with its operands' shapes. A predicate denotes all of its sort or nothing, so
/// it never equals one value; a connective over terms denotes a set of values.
const MIXED_EQUALITIES: &[(&str, &str)] = &[
    ("{ {X #Equals 1} #Equals true }", "predicate, Bool term"),
    (
        "{ #Ceil(1 /Int (X -Int 1)) #Equals true }",
        "predicate, Bool term",
    ),
    (
        "#Not({ {X #Equals 1} #Equals true })",
        "predicate, Bool term",
    ),
    ("{ {X #Equals 1} #Equals false }", "predicate, Bool term"),
    (
        "(X >Int 0) #And { (X >Int 5) #Equals #Ceil(1 /Int X) }",
        "Bool term, predicate",
    ),
    (
        "{ true #Equals ((X ==Int 1) #Or (X ==Int 2)) }",
        "Bool term, connective",
    ),
    (
        "{ ((X ==Int 1) #And (X ==Int 2)) #Equals false }",
        "connective, Bool term",
    ),
    // {X = 1} = {X = 1, false} holds where X ≠ 1: an equality of two sets of values.
    (
        "{ ((X ==Int 1) #Or (X ==Int 1)) #Equals ((X ==Int 1) #Or false) }",
        "connective, connective",
    ),
    (
        "{ ((X ==Int 1) #Or (X ==Int 2)) #Equals {X #Equals 1} }",
        "connective, predicate",
    ),
    ("{ X #Equals (1 #Or 2) }", "Int term, connective"),
];

/// The first line of the probed sentence: the line after [`HEADER`] and any declarations.
fn line_after(prefix: &str) -> usize {
    HEADER.lines().count() + prefix.lines().count() + 1
}

fn try_compile(sentences: &str) -> Result<String, String> {
    let source = format!("{HEADER}{sentences}endmodule\n");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![
            embedded("kast.md").unwrap(),
            embedded("prelude.md").unwrap(),
        ],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("ml_conditions.k", source),
        "P",
        Some("P-SYNTAX"),
        &mut resolver,
        &options,
    )
    .expect("the definition loads");
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map(|artifacts| artifacts.definition_kore)
        .map_err(|error| rendered(&error))
}

/// A compile error with its diagnostics, one per line as `source:line:column: code: message`.
fn rendered(error: &k_rust::kompile::CompileError) -> String {
    let mut text = error.to_string();
    for diagnostic in &error.diagnostics {
        let at = diagnostic
            .location
            .map(|location| format!("{}:{}", location.start_line, location.start_column))
            .unwrap_or_default();
        text.push_str(&format!(
            "\n{}:{at}: {}: {}",
            diagnostic.source.as_deref().unwrap_or(""),
            diagnostic.code.as_str(),
            diagnostic.message
        ));
    }
    text
}

/// `kcompile --for-proving` of module P-SPEC (`claims`) over P (`sentences`).
fn try_compile_spec(sentences: &str, claims: &str) -> Result<String, String> {
    try_compile_spec_source(format!(
        "{HEADER}{sentences}endmodule\n\nmodule P-SPEC\n  imports P\n{claims}endmodule\n"
    ))
}

/// The specification `source` (main module `P-SPEC`, definition module `P`), compiled.
fn try_compile_spec_source(source: String) -> Result<String, String> {
    try_compile_spec_source_for(source, CompilationBackend::Rust)
}

/// The specification `source` compiled for `backend` (see [`try_compile_spec_source`]).
fn try_compile_spec_source_for(
    source: String,
    backend: CompilationBackend,
) -> Result<String, String> {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("ml_conditions.k", source),
        "P-SPEC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            configuration_module: Some("P".to_owned()),
            ..backend.load_options()
        },
    )
    .expect("the specification loads");
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: "P".to_owned(),
            },
            ..CompileOptions::default()
        },
    )
    .map(|artifacts| artifacts.definition_kore)
    .map_err(|error| rendered(&error))
}

/// The refusal is the matching-logic position diagnostic located at the sentence (`sentence`
/// names it), and states both reasons.
#[track_caller]
fn assert_refused(
    result: Result<String, String>,
    sentence: &str,
    line: usize,
    shapes: &str,
    condition: &str,
) {
    let message = match result {
        Ok(_) => panic!("{condition}: the {sentence} compiles"),
        Err(message) => message,
    };
    let at = format!("ml_conditions.k:{line}:3: MlConstructPosition: ");
    assert!(
        message.contains(&at),
        "{condition}: the {sentence} is not refused at {at:?}: {message}"
    );
    for reason in [
        "a predicate at sort Bool denotes all of Bool or nothing",
        "a connective over terms denotes a set of values",
    ] {
        assert!(
            message.contains(reason),
            "{condition} ({shapes}): no {reason:?} in {message}"
        );
    }
    assert!(
        message.contains("andBool"),
        "{condition}: no remedy in {message}"
    );
}

#[test]
fn a_rule_whose_condition_has_a_mixed_equality_is_refused() {
    for (condition, shapes) in MIXED_EQUALITIES {
        let result = try_compile(&format!(
            "  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n"
        ));
        assert_refused(result, "rule [P.p]", line_after(""), shapes, condition);
    }
}

#[test]
fn a_function_equation_whose_condition_has_a_mixed_equality_is_refused() {
    for (condition, shapes) in MIXED_EQUALITIES {
        let result = try_compile(&format!(
            "{F}  rule [p]: f(X) => X requires {condition}\n{G}"
        ));
        assert_refused(result, "rule [P.p]", line_after(F), shapes, condition);
    }
    // In an ensures, at the equation's sort.
    let (condition, shapes) = MIXED_EQUALITIES[0];
    let result = try_compile(&format!(
        "{F}  rule [p]: f(X) => X ensures {condition}\n{G}"
    ));
    assert_refused(result, "rule [P.p]", line_after(F), shapes, condition);
}

#[test]
fn a_claim_whose_condition_has_a_mixed_equality_is_refused() {
    let rule = "  rule [g]: <k> go(X) => done(X) ... </k> requires X =/=Int 1\n";
    // The claim's line: HEADER, the rule, `endmodule`, a blank line, `module P-SPEC`, `imports P`.
    let line = HEADER.lines().count() + 1 + 4 + 1;
    for (condition, shapes) in MIXED_EQUALITIES {
        let result = try_compile_spec(
            rule,
            &format!("  claim [q]: <k> go(X) => done(X) ... </k> requires {condition}\n"),
        );
        assert_refused(result, "claim [P-SPEC.q]", line, shapes, condition);
    }
}

/// An owise equation reads its competitors' conditions; the refusal names the competitor. The owise
/// rule comes first, so its emission meets the competitor's condition before the competitor's own
/// emission does; that the owise route itself refuses it, with no help from the competitor's
/// emission, is the unit test `the_owise_route_refuses_a_competitor_condition_with_a_mixed_equality`
/// in module_to_kore/equations.rs.
#[test]
fn an_owise_competitor_whose_condition_has_a_mixed_equality_is_refused() {
    let (condition, shapes) = MIXED_EQUALITIES[0];
    let result = try_compile(&format!(
        "{F}  rule [o]: f(_) => 0 [owise]\n  rule [p]: f(X) => 1 requires {condition}\n{G}"
    ));
    assert_refused(result, "rule [P.p]", line_after(F) + 1, shapes, condition);
}

/// `go(1) #Or go(2)` at a KItem position is a connective under a sort injection
/// (`inj{SortPgm{}, SortKItem{}}(\or{SortPgm{}}(..))`); `inj` is the identity on values, so the
/// equality still compares a value with a set of values and is refused, in each sentence kind.
#[test]
fn an_injected_connective_in_a_condition_equality_is_refused() {
    const C: &str = "{ K #Equals (go(1) #Or go(2)) }";
    let result = try_compile(&format!(
        "  rule [p]: <k> K:KItem => done(0) ... </k> requires {C}\n"
    ));
    assert_refused(
        result,
        "rule [P.p]",
        line_after(""),
        "KItem term, injected connective",
        C,
    );
    let h = "  syntax Int ::= h(KItem) [function, symbol(h)]\n";
    let result = try_compile(&format!("{h}  rule [p]: h(K) => 0 requires {C}\n"));
    assert_refused(
        result,
        "rule [P.p]",
        line_after(h),
        "KItem term, injected connective",
        C,
    );
    let line = HEADER.lines().count() + 1 + 4 + 1;
    let result = try_compile_spec(
        "  rule [g]: <k> go(X) => done(X) ... </k>\n",
        &format!("  claim [q]: <k> K:KItem => done(0) ... </k> requires {C}\n"),
    );
    assert_refused(
        result,
        "claim [P-SPEC.q]",
        line,
        "KItem term, injected connective",
        C,
    );
}

/// An equality of two predicates is their iff, and an equality of two terms an equality of
/// values: both are conditions, and compile.
#[test]
fn equalities_of_two_predicates_or_two_terms_compile() {
    for condition in [
        "{ {X #Equals 1} #Equals #Ceil(1 /Int X) }",
        "{ true #Equals (X ==Int 1) }",
        "{ (X ==Int 1) #Equals (X >Int 0) }",
    ] {
        let kore = try_compile(&format!(
            "  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n"
        ))
        .unwrap_or_else(|message| panic!("{condition}: {message}"));
        assert!(kore.contains("label{}(\"P.p\")"), "{condition}");
    }
}

/// The LLVM target keeps its output, these conditions included.
#[test]
fn the_llvm_target_compiles_a_mixed_equality_as_before() {
    for (condition, _) in MIXED_EQUALITIES {
        let kore = compile_for(
            &format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n"),
            CompilationBackend::Llvm,
        );
        // The whole condition stays one Bool term, as before.
        assert_contains(
            &axiom(&kore, "P.p"),
            &format!("\\equals{{SortBool{{}}, {TOP}}}("),
        );
    }
}

// ---------------------------------------------------------------- disjunctions in conditions

/// The variables named like a guard alias (`_Gen<N>`) that `term` holds.
fn generated_variables(term: &Term) -> Vec<String> {
    let mut names = Vec::new();
    term.visit_preorder(&mut |node| {
        if let Term::Variable { name, .. } = node.unannotated()
            && name.starts_with("_Gen")
            && !names.contains(name)
        {
            names.push(name.clone());
        }
    });
    names
}

/// A condition is matched against nothing, so no variable that only a condition holds can name a
/// matched term: every generated variable of a compiled rule's or context's conditions is one of
/// its body's. `sentences` hold no anonymous variable, the other source of `_Gen` names.
#[track_caller]
fn assert_conditions_hold_no_alias(sentences: &str) {
    let artifacts = compile_artifacts(sentences, CompilationBackend::Rust);
    let mut checked = 0;
    for module in &artifacts.execution_definition.modules {
        for sentence in &module.local_sentences {
            let (body, conditions) = match sentence.as_ref() {
                Sentence::Rule {
                    body,
                    requires,
                    ensures,
                    ..
                } => (body, vec![requires, ensures]),
                Sentence::Context { body, requires, .. } => (body, vec![requires]),
                _ => continue,
            };
            let bound = generated_variables(body);
            for condition in conditions {
                checked += 1;
                for name in generated_variables(condition) {
                    assert!(
                        bound.contains(&name),
                        "the condition {condition:?} holds {name}, which its body {body:?} does not hold"
                    );
                }
            }
        }
    }
    assert!(checked > 0, "no rule was compiled");
}

const ONE_OR_TWO: &str = "(X ==Int 1) #Or (X ==Int 2)";

/// An equation whose condition is a disjunction of Bool terms applies wherever one of them is
/// true: f(1) and f(2) are 1, and f(3) has no equation that applies.
#[test]
fn an_equation_with_a_bool_term_disjunction_in_its_requires_applies() {
    let sentences = format!("{F}  rule [p]: f(X) => 1 requires {ONE_OR_TWO}\n{G}");
    assert_eq!(run(&sentences, 1), stuck("done(1)"));
    assert_eq!(run(&sentences, 2), stuck("done(1)"));
    let three = run(&sentences, 3);
    assert!(
        three.contains(&("Stuck".to_owned(), "done(f(3))".to_owned())),
        "f(3) stays unevaluated: {three:?}"
    );
    assert!(
        !three.iter().any(|(_, term)| term == "done(1)"),
        "{three:?}"
    );
}

/// The same disjunction introduced by a macro is the same condition.
#[test]
fn a_macro_introduced_disjunction_gives_the_same_equation() {
    let direct = format!("{F}  rule [p]: f(X) => 1 requires {ONE_OR_TWO}\n{G}");
    let macro_sentences = format!(
        "  syntax Bool ::= oneOrTwo(Int) [macro]\n  rule oneOrTwo(X) => {ONE_OR_TWO}\n{F}  rule [p]: f(X) => 1 requires oneOrTwo(X)\n{G}"
    );
    for n in 1..=3 {
        assert_eq!(run(&macro_sentences, n), run(&direct, n), "go({n})");
    }
}

/// A rewrite rule with a Bool-term disjunction in its requires steps exactly where it holds, and
/// its leaf carries no constraint over a variable the condition introduced.
#[test]
fn a_rule_with_a_bool_term_disjunction_steps_without_a_residual_alias() {
    let sentences = format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {ONE_OR_TWO}\n");
    for n in [1, 2] {
        let leaves = run_states(&sentences, n);
        assert_eq!(leaves.len(), 1, "go({n}): {leaves:?}");
        let (reason, k, state) = &leaves[0];
        assert_eq!(
            (reason.as_str(), k.as_str()),
            ("Stuck", format!("done({n})").as_str())
        );
        assert!(!state.contains("Unds'Gen"), "go({n}): {state}");
    }
    assert_eq!(run(&sentences, 3), stuck("go(3)"));
}

/// An existential ensures that is a disjunction: the step reaches done(?W) under that
/// disjunction (no alias states it false on every instance).
#[test]
fn an_existential_ensures_disjunction_constrains_the_new_value() {
    let sentences =
        "  rule [p]: <k> go(0) => done(?W) ... </k> ensures (?W ==Int 1) #Or (?W ==Int 2)\n";
    let leaves = run_states(sentences, 0);
    // A build that cannot decide whether the ensures is satisfiable may also report the step as
    // possibly undefined (Trivial at the pre-state); the meaning neither requires nor excludes it.
    let (reached, undecided): (Vec<_>, Vec<_>) = leaves
        .iter()
        .partition(|(reason, _, _)| reason != "Trivial");
    assert!(undecided.iter().all(|(_, k, _)| k == "go(0)"), "{leaves:?}");
    assert_eq!(reached.len(), 1, "{leaves:?}");
    let (reason, k, state) = reached[0];
    assert_eq!((reason.as_str(), k.as_str()), ("Stuck", "done(var)"));
    assert!(
        state.contains(&int("1")) && state.contains(&int("2")),
        "{state}"
    );
    assert!(!state.contains("Unds'Gen"), "{state}");
}

/// No compiled condition holds a guard alias: rule, equation, simplification and context
/// conditions with a disjunction, and a rule with a disjunction at a shared position (outside its
/// rewrite, so the right side reuses the matched term through the alias) beside a disjunction in
/// its requires.
#[test]
fn compiled_conditions_hold_no_guard_alias() {
    let conditions = [
        ONE_OR_TWO,
        "{X #Equals 1} #Or {X #Equals 2}",
        "{X #Equals 1} #Or (X ==Int 2)",
        "#Forall Y:Int . (#Not({Y #Equals X}) #Or {Y #Equals X})",
    ];
    for condition in conditions {
        assert_conditions_hold_no_alias(&format!(
            "  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n"
        ));
        assert_conditions_hold_no_alias(&format!(
            "{F}  rule [p]: f(X) => X requires {condition}\n{G}"
        ));
        assert_conditions_hold_no_alias(&format!(
            "{F}  rule [p]: f(X) => X requires {condition} [simplification]\n{G}"
        ));
    }
    assert_conditions_hold_no_alias(
        "  syntax Exp ::= Int | e(Int) [symbol(e)]\n  syntax KResult ::= Int\n  syntax KItem ::= c2(Int, Exp) [symbol(c2)]\n  rule [e]: <k> e(N) => N ... </k>\n  rule [g]: <k> go(N) => c2(N, e(N)) ... </k>\n  context [p]: c2(N:Int, HOLE:Exp) requires (N ==Int 1) #Or (N ==Int 2)\n",
    );
    let shared = format!(
        "  syntax KItem ::= pair(Int, Int) [symbol(pair)]\n  rule [p]: <k> pair(1 #Or 2, (X => 0)) ... </k> requires {ONE_OR_TWO}\n"
    );
    assert_conditions_hold_no_alias(&shared);
    let artifacts = compile_artifacts(&shared, CompilationBackend::Rust);
    let aliased = artifacts
        .execution_definition
        .modules
        .iter()
        .filter(|module| module.name == "P")
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match sentence.as_ref() {
            Sentence::Rule { body, .. } => Some(generated_variables(body)),
            _ => None,
        })
        .filter(|names| !names.is_empty())
        .count();
    assert_eq!(aliased, 1, "the shared disjunction keeps its alias");
}

// ---------------------------------------------------------------- predicate context conditions

/// `go(N)` steps to `foo(N, e(N))`; the context heats `e(N)` only where its condition holds,
/// `e(N)` evaluates to `N`, which cools back: `foo(N, N)`.
fn foo_context(condition: &str) -> String {
    format!(
        "  syntax Exp ::= Int | e(Int) [symbol(e)]\n  syntax KResult ::= Int\n  syntax KItem ::= foo(Int, Exp) [symbol(foo)]\n  rule [e]: <k> e(N) => N ... </k>\n  rule [g]: <k> go(N) => foo(N, e(N)) ... </k>\n  context [p]: foo(N:Int, HOLE:Exp) requires {condition}\n"
    )
}

/// A context whose condition is a predicate heats exactly where the predicate holds.
#[test]
fn a_predicate_context_heats_only_where_it_holds() {
    for condition in [
        "{HOLE #Equals e(1)}",
        "{N #Equals 1}",
        "(N ==Int 1) #Or (N ==Int 2)",
    ] {
        let sentences = foo_context(condition);
        assert_eq!(run(&sentences, 1), stuck("foo(1, 1)"), "{condition}");
        assert_eq!(run(&sentences, 3), stuck("foo(3, e(3))"), "{condition}");
    }
}

/// A context whose condition is a Bool term keeps it as one Bool conjunct beside the heating
/// test (`_andBool_`), as before predicate conditions were conjoined as predicates.
#[test]
fn a_bool_context_condition_stays_a_bool_conjunct() {
    let sentences = foo_context("N ==Int 1");
    let kore = compile(&sentences);
    let heat = axiom(&kore, "P.p-heat");
    // The whole requires is one Bool leaf whose term is the `_andBool_` conjunction.
    assert_contains(
        &heat,
        &format!(
            "\\equals{{SortBool{{}}, {TOP}}}(Lbl'Unds'andBool'Unds'{{}}({}, LblnotBool'Unds'{{}}(",
            eq_int("VarN:SortInt{}", &int("1"))
        ),
    );
    assert_lacks(&heat, "\\and{SortGeneratedTopCell{}}(\\equals{SortBool{}");
    assert_eq!(run(&sentences, 1), stuck("foo(1, 1)"));
    assert_eq!(run(&sentences, 3), stuck("foo(3, e(3))"));
}

/// Macros, aliases and semantic casts that state a predicate condition. The conjunction a context
/// gains is chosen on the condition the backend reads, after expansion and cast resolution, so
/// each spelling heats exactly where its predicate holds, as the direct spelling does.
const SPELLED_PREDICATES: &str = "  syntax Bool ::= isOne(Int) [macro]\n  rule isOne(N) => {N #Equals 1}\n  syntax Bool ::= isOneAlias(Int) [alias]\n  rule isOneAlias(N) => {N #Equals 1}\n  syntax Bool ::= small(Int) [macro]\n  rule small(N) => (N ==Int 1) #Or (N ==Int 2)\n";

#[test]
fn a_predicate_context_condition_spelled_through_a_macro_an_alias_or_a_cast_heats_where_it_holds() {
    for (condition, heats_at_two) in [
        ("isOne(N)", false),
        ("isOneAlias(N)", false),
        ("({N #Equals 1}):Bool", false),
        ("small(N)", true),
    ] {
        let sentences = format!("{SPELLED_PREDICATES}{}", foo_context(condition));
        assert_eq!(run(&sentences, 1), stuck("foo(1, 1)"), "{condition}");
        let two = if heats_at_two {
            "foo(2, 2)"
        } else {
            "foo(2, e(2))"
        };
        assert_eq!(run(&sentences, 2), stuck(two), "{condition}");
        assert_eq!(run(&sentences, 3), stuck("foo(3, e(3))"), "{condition}");
    }
}

/// A strict production heats through its context alias, whose condition here is a predicate
/// spelled through a macro: `#Top` lets every argument heat, `#Bottom` none.
#[test]
fn a_strict_alias_condition_spelled_through_a_macro_is_conjoined_as_a_predicate() {
    let strict = "  syntax Exp ::= Int | e(Int) [symbol(e)] | bar(Exp) [strict(c), symbol(bar)]\n  syntax KResult ::= Int\n  rule [e]: <k> e(N) => N ... </k>\n  rule [g]: <k> go(N) => bar(e(N)) ... </k>\n  syntax Bool ::= always() [macro] | never() [macro]\n  rule always() => #Top\n  rule never() => #Bottom\n";
    for (condition, leaf) in [("always()", "bar(1)"), ("never()", "bar(e(1))")] {
        let sentences =
            format!("{strict}  context alias [c]: <k> HERE ... </k> requires {condition}\n");
        assert_eq!(run(&sentences, 1), stuck(leaf), "{condition}");
    }
}

/// The search-pattern route chooses the conjunction of its sort tests with the condition after
/// macro expansion too: a predicate spelled through a macro compiles to the pattern its direct
/// spelling compiles to.
#[test]
fn a_search_pattern_condition_spelled_through_a_macro_compiles_as_its_expansion() {
    let sentences = format!("{SPELLED_PREDICATES}  syntax KItem ::= box(Int) [symbol(box)]\n");
    let direct = compile_pattern(&sentences, "<k> box(X:Int) </k> requires {X #Equals 1}");
    for spelled in ["isOne(X)", "isOneAlias(X)"] {
        let pattern = format!("<k> box(X:Int) </k> requires {spelled}");
        assert_eq!(compile_pattern(&sentences, &pattern), direct, "{spelled}");
    }
}

/// `contents` compiled as a search pattern of the definition `sentences`, as KORE text.
fn compile_pattern(sentences: &str, contents: &str) -> String {
    let compiled = try_compile_pattern_source(format!("{HEADER}{sentences}endmodule\n"), contents)
        .unwrap_or_else(|error| panic!("{contents}: {error}"));
    Printer::compact().print_pattern(&compiled)
}

/// `contents` compiled as a search pattern of the whole definition `source` (main module `P`,
/// syntax module `P-SYNTAX`), the pattern written on line 1 of `<pattern>`.
fn try_compile_pattern_source(
    source: String,
    contents: &str,
) -> Result<Pattern, CompileSearchPatternError> {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![
            embedded("kast.md").unwrap(),
            embedded("prelude.md").unwrap(),
        ],
        ..CompilationBackend::Rust.load_options()
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("ml_conditions.k", source),
        "P",
        Some("P-SYNTAX"),
        &mut resolver,
        &options,
    )
    .expect("the definition loads");
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("the definition compiles");
    let parsing = definition_with_named_projections(loaded.definition());
    let parsing = ResolvedDefinition::resolve(&parsing).unwrap();
    let execution = ResolvedDefinition::resolve(&artifacts.execution_definition).unwrap();
    let mut attributes = Attributes::default();
    attributes.insert(SOURCE_ATTRIBUTE, serde_json::json!("<pattern>"));
    attributes.insert(
        LOCATION_ATTRIBUTE,
        serde_json::json!([1, 1, 1, contents.len() + 1]),
    );
    compile_search_pattern(&parsing, &execution, "P", contents, attributes)
        .map(|compiled| compiled.pattern)
}

/// An anonymous existential in an ensures (`?_`) is renamed like `_`; the renamed variable is the
/// authored one, so the stage checker (C1 in the test profile) accepts it, and the rule runs as
/// its named spelling does.
#[test]
fn an_anonymous_existential_in_an_ensures_compiles_and_runs_as_a_named_one() {
    let anonymous = run(
        "  rule [p]: <k> go(X) => done(X) ... </k> ensures ?_ ==Int 1\n",
        1,
    );
    let named = run(
        "  rule [p]: <k> go(X) => done(X) ... </k> ensures ?W ==Int 1\n",
        1,
    );
    assert_eq!(anonymous, named);
    assert!(
        anonymous.contains(&("Stuck".to_owned(), "done(1)".to_owned())),
        "{anonymous:?}"
    );
}

// ---------------------------------------------------------------- the configuration in conditions

/// A definition whose configuration has a `<flag>` cell, which `isZero()` reads; `isZeroM()` is a
/// macro for it, so macro expansion inlines a condition that reads the configuration.
const FLAG_HEADER: &str = "module P-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <flag> $FLAG:Int </flag>
  syntax KItem ::= done(Int) [symbol(done)]
  syntax Bool ::= isZero() [function, symbol(isZero)]
  rule [[ isZero() => F ==Int 0 ]] <flag> F </flag>
  syntax Bool ::= isZeroM() [macro]
  rule isZeroM() => isZero()
";

/// The leaves of go(n) with `<flag>` holding `flag`: halt reason and the first item of `<k>`.
fn run_with_flag(sentences: &str, n: i64, flag: i64) -> Vec<(String, String)> {
    let kore = compile_source(
        format!("{FLAG_HEADER}{sentences}endmodule\n"),
        CompilationBackend::Rust,
    )
    .definition_kore;
    let mut backend = Backend::new(&kore, "P", BackendOptions::default()).unwrap();
    let state = parse_pattern(&format!(
        "Lbl'-LT-'generatedTop'-GT-'{{}}(Lbl'-LT-'k'-GT-'{{}}(kseq{{}}(inj{{SortPgm{{}}, SortKItem{{}}}}(Lblgo{{}}({})), dotk{{}}())), Lbl'-LT-'flag'-GT-'{{}}({}), Lbl'-LT-'generatedCounter'-GT-'{{}}({}))",
        int(&n.to_string()),
        int(&flag.to_string()),
        int("0")
    ))
    .unwrap();
    let result = backend
        .execute(ExecuteRequest {
            max_depth: Some(5),
            ..ExecuteRequest::new(state)
        })
        .unwrap();
    let mut leaves: Vec<(String, String)> = result
        .leaves
        .iter()
        .map(|leaf| {
            let state = codec::from_value(&leaf.state).unwrap();
            (format!("{:?}", leaf.reason), k_cell(&state))
        })
        .collect();
    leaves.sort();
    leaves
}

/// `#Configuration` names the current configuration, which `resolve function configuration`
/// passes to `isZero` in the macro's right side and macro expansion then inlines into a
/// condition; it is a free variable of no condition until the configuration-binding stage binds
/// it, so the stage checker (C1 in the test profile) accepts each of these, and each condition
/// reads the `<flag>` cell.
#[test]
fn a_rule_requires_reading_the_configuration_through_a_macro_compiles_and_reads_it() {
    let rule = "  rule [g]: <k> go(N) => done(N) ... </k> requires isZeroM()\n";
    assert_eq!(run_with_flag(rule, 3, 0), stuck("done(3)"));
    assert_eq!(run_with_flag(rule, 3, 1), stuck("go(3)"));
}

#[test]
fn a_context_requires_reading_the_configuration_through_a_macro_compiles_and_reads_it() {
    let context = "  syntax Exp ::= Int | e(Int) [symbol(e)]\n  syntax KResult ::= Int\n  syntax KItem ::= foo(Int, Exp) [symbol(foo)]\n  rule [e]: <k> e(N) => N ... </k>\n  rule [g]: <k> go(N) => foo(N, e(N)) ... </k>\n  context [p]: foo(_:Int, HOLE:Exp) requires isZeroM()\n";
    assert_eq!(run_with_flag(context, 3, 0), stuck("foo(3, 3)"));
    assert_eq!(run_with_flag(context, 3, 1), stuck("foo(3, e(3))"));
}

#[test]
fn an_ensures_reading_the_configuration_through_a_macro_compiles_and_reads_it() {
    let ensures = "  rule [g]: <k> go(N) => done(N) ... </k> ensures isZeroM()\n";
    assert_eq!(run_with_flag(ensures, 3, 0), stuck("done(3)"));
    // With a nonzero flag the ensures is false, so the step has no successor: its result is
    // empty, which the backend reports as a Trivial leaf at the pre-state.
    assert_eq!(
        run_with_flag(ensures, 3, 1),
        vec![("Trivial".to_owned(), "go(3)".to_owned())]
    );
}

// ---------------------------------------------------------------- a conjunction of two terms

// For terms t1 and t2 that denote at most one value each, `t1 #And t2` is {a} ∩ {b}: a where
// a = b, nothing otherwise, which is `t1 #And {t1 #Equals t2}`. A built conjunction of two
// connective-free terms, and one in a claim's left side, is compiled in that form; an operand
// that holds a connective may denote several values, where the identity does not hold, and a
// matched conjunction unifies as written.

fn trivial(term: &str) -> Vec<(String, String)> {
    vec![("Trivial".to_owned(), term.to_owned())]
}

/// `\and{SortInt{}}(t1, \equals{SortInt{}, SortInt{}}(t1, t2))`: `t1 #And t2` lowered.
fn lowered(t1: &str, t2: &str) -> String {
    format!("\\and{{SortInt{{}}}}({t1}, \\equals{{SortInt{{}}, SortInt{{}}}}({t1}, {t2}))")
}

#[test]
fn a_built_conjunction_of_two_terms_is_the_first_guarded_by_their_equality() {
    let rule = "  rule [p]: <k> go(X) => done(X #And 1) ... </k>\n";
    let axiom = axiom(&compile(rule), "P.p");
    assert_contains(&axiom, &format!("Lbldone{{}}({})", lowered(X, &int("1"))));
    assert_eq!(run(rule, 1), stuck("done(1)"));
    assert_eq!(run(rule, 3), trivial("go(3)"));
}

#[test]
fn a_built_conjunction_with_a_function_application_is_lowered_and_runs_by_its_meaning() {
    let rule =
        format!("{F}  rule [f]: f(X) => X\n  rule [p]: <k> go(X) => done(f(X) #And 3) ... </k>\n");
    let axiom = axiom(&compile(&rule), "P.p");
    assert_contains(
        &axiom,
        &format!(
            "Lbldone{{}}({})",
            lowered("Lblf{}(VarX:SortInt{})", &int("3"))
        ),
    );
    assert_eq!(run(&rule, 3), stuck("done(3)"));
    assert_eq!(run(&rule, 1), trivial("go(1)"));
}

#[test]
fn a_conjunction_in_a_macro_right_side_is_lowered_where_the_macro_is_used() {
    let rule = "  syntax Int ::= m(Int) [macro, symbol(m)]\n  rule [m]: m(X) => X #And 1\n  rule [p]: <k> go(X) => done(m(X)) ... </k>\n";
    let axiom = axiom(&compile(rule), "P.p");
    assert_contains(&axiom, &format!("Lbldone{{}}({})", lowered(X, &int("1"))));
    assert_eq!(run(rule, 1), stuck("done(1)"));
    assert_eq!(run(rule, 3), trivial("go(3)"));
}

/// `(X #Or 0) #And 1` is {X, 0} ∩ {1}, which `(X #Or 0) #And {(X #Or 0) #Equals 1}` is not
/// ({X, 0} = {1} never holds), so it is emitted as written.
#[test]
fn a_built_conjunction_whose_operand_holds_a_connective_is_not_lowered() {
    // The Rust target refuses the sentence at compile
    // (`a_built_conjunction_whose_operand_holds_a_connective_is_refused`); the LLVM target's
    // KORE shows that the stage leaves it as written.
    let axiom = axiom(
        &compile_for(
            "  rule [p]: <k> go(X) => done((X #Or 0) #And 1) ... </k>\n",
            CompilationBackend::Llvm,
        ),
        "P.p",
    );
    assert_contains(
        &axiom,
        &format!(
            "Lbldone{{}}(\\and{{SortInt{{}}}}(\\or{{SortInt{{}}}}({X}, {}), {}))",
            int("0"),
            int("1")
        ),
    );
    assert_lacks(&axiom, "\\equals{");
}

#[test]
fn a_built_conjunction_of_a_term_and_a_predicate_is_unchanged() {
    let rule = "  rule [p]: <k> go(X) => done(X #And {X #Equals 1}) ... </k>\n";
    let axiom = axiom(&compile(rule), "P.p");
    assert_contains(&axiom, &format!("Lbldone{{}}({})", lowered(X, &int("1"))));
    assert_eq!(axiom.matches("\\equals{").count(), 1, "{axiom}");
    assert_eq!(run(rule, 1), stuck("done(1)"));
    assert_eq!(run(rule, 3), trivial("go(3)"));
}

#[test]
fn a_matched_conjunction_of_two_terms_is_unchanged() {
    let rule = "  rule [p]: <k> go(X #And 1) => done(X) ... </k>\n";
    let axiom = axiom(&compile(rule), "P.p");
    assert_contains(
        &axiom,
        &format!("Lblgo{{}}(\\and{{SortInt{{}}}}({X}, {}))", int("1")),
    );
    assert_lacks(&axiom, "\\equals{");
    assert_eq!(run(rule, 1), stuck("done(1)"));
    assert_eq!(run(rule, 3), stuck("go(3)"));
}

#[test]
fn a_claim_left_side_conjunction_of_two_terms_and_alias_are_lowered() {
    let rule = "  rule [g]: <k> go(X) => done(X) ... </k> requires X <Int 3\n";
    let kore = try_compile_spec(
        rule,
        "  claim [c]: <k> go(X #And 1) => done(?_) ... </k>\n  claim [d]: <k> go(X #as Y) => done(?_) ... </k>\n",
    )
    .expect("the specification compiles");
    assert_contains(
        &axiom(&kore, "P-SPEC.c"),
        &format!("Lblgo{{}}({})", lowered(X, &int("1"))),
    );
    assert_contains(
        &axiom(&kore, "P-SPEC.d"),
        &format!("Lblgo{{}}({})", lowered(X, "VarY:SortInt{}")),
    );
}

/// The annotated `#Equals` nodes of `term`, with their annotations.
fn annotated_equalities(term: &Term, found: &mut Vec<Term>) {
    match term {
        Term::Annotated { term: inner, .. } => {
            if matches!(inner.unannotated(), Term::Apply { label, .. } if label.name == "#Equals") {
                found.push(term.clone());
            }
            annotated_equalities(inner, found);
        }
        Term::Apply { arguments, .. } | Term::Sequence(arguments) => {
            for argument in arguments {
                annotated_equalities(argument, found);
            }
        }
        Term::Rewrite { left, right } => {
            annotated_equalities(left, found);
            annotated_equalities(right, found);
        }
        Term::As { pattern, alias } => {
            annotated_equalities(pattern, found);
            annotated_equalities(alias, found);
        }
        Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
    }
}

/// The lowering generates the equality, so the equality records it as its origin; the copy of the
/// first operand keeps that operand's source position. A function equation has no cells, so no
/// later stage rebuilds its right side: in a rule, cell concretization rebuilds the `<k>` cell and
/// receipts every node of it, the equality included, under its own pass.
#[test]
fn a_generated_equality_records_the_lowering_as_its_origin() {
    // A chain of n operands generates n - 1 equalities, each with its own copy of X.
    for (conjunction, n) in [("X #And 1", 2), ("X #And 1 #And 2", 3)] {
        let artifacts = compile_artifacts(
            &format!("{F}  rule [p]: f(X) => {conjunction}\n{G}"),
            CompilationBackend::Rust,
        );
        let mut equalities = Vec::new();
        for module in &artifacts.execution_definition.modules {
            if module.name != "P" {
                continue;
            }
            for sentence in &module.local_sentences {
                if let Sentence::Rule { body, .. } = &**sentence {
                    annotated_equalities(body, &mut equalities);
                }
            }
        }
        assert_eq!(
            equalities.len(),
            n - 1,
            "{conjunction}: generated equalities in module P"
        );
        for equality in &equalities {
            let origin = equality
                .metadata()
                .and_then(|metadata| metadata.origin.as_deref())
                .expect("the generated equality has an origin");
            assert_eq!(origin.pass.as_str(), "lower-term-conjunctions");
            assert_eq!(
                GeneratingPass::from_name("lower-term-conjunctions"),
                Some(origin.pass)
            );
            let Term::Apply { arguments, .. } = equality.unannotated() else {
                unreachable!("an equality is an application")
            };
            let copy = arguments[0].metadata().expect("the copy of X is annotated");
            let span = copy
                .span
                .unwrap_or_else(|| panic!("the copy of X keeps its source position: {copy:?}"));
            // The copy is a node the lowering creates: its origin names the pass and links X's
            // span.
            let origin = copy.origin.as_deref().expect("the copy of X has an origin");
            assert_eq!(origin.pass.as_str(), "lower-term-conjunctions");
            assert!(
                origin
                    .origins
                    .links()
                    .contains(&ProvenanceLink::Source { span }),
                "the copy's origin links X's span {span:?}: {:?}",
                origin.origins.links()
            );
        }
    }
}

fn chain(third: &str) -> String {
    format!("  rule [p]: <k> go(X) => done(X #And 1 #And {third}) ... </k>\n")
}

/// A chain `t1 #And t2 #And ... #And tn` of connective-free terms is their intersection, which
/// denotes at most one value, so it is t1 guarded by the equality of t1 with each other operand.
/// `X #And 1 #And 2` (parsed `(X #And 1) #And 2`) denotes nothing at every X.
#[test]
fn a_built_conjunction_chain_of_distinct_terms_denotes_nothing() {
    let rule = chain("2");
    assert_eq!(run(&rule, 1), trivial("go(1)"));
    assert_eq!(run(&rule, 2), trivial("go(2)"));
    let equals = |value: &str| format!("\\equals{{SortInt{{}}, SortInt{{}}}}({X}, {})", int(value));
    assert_contains(
        &axiom(&compile(&rule), "P.p"),
        &format!(
            "Lbldone{{}}(\\and{{SortInt{{}}}}(\\and{{SortInt{{}}}}({X}, {}), {}))",
            equals("1"),
            equals("2")
        ),
    );
}

/// `X #And 1 #And 1` is 1 at X = 1 and nothing elsewhere, grouped either way.
#[test]
fn a_built_conjunction_chain_of_equal_terms_is_their_value() {
    let rule = chain("1");
    assert_eq!(run(&rule, 1), stuck("done(1)"));
    assert_eq!(run(&rule, 3), trivial("go(3)"));
    let right = "  rule [p]: <k> go(X) => done(X #And (1 #And 1)) ... </k>\n";
    assert_eq!(run(right, 1), stuck("done(1)"));
    assert_eq!(run(right, 3), trivial("go(3)"));
}

/// A predicate operand denotes everything or nothing, so it cannot enlarge the intersection:
/// `(t1 #And {P}) #And t2` is `t1 #And {P} #And {t1 #Equals t2}`, the predicate kept as written.
#[test]
fn a_built_conjunction_chain_with_a_predicate_operand_guards_its_terms() {
    let rule = "  rule [p]: <k> go(X) => done(X #And {X #Equals 1} #And 1) ... </k>\n";
    assert_eq!(run(rule, 1), stuck("done(1)"));
    assert_eq!(run(rule, 2), trivial("go(2)"));
    let equals = |value: &str| format!("\\equals{{SortInt{{}}, SortInt{{}}}}({X}, {})", int(value));
    assert_contains(
        &axiom(&compile(rule), "P.p"),
        &format!(
            "Lbldone{{}}(\\and{{SortInt{{}}}}(\\and{{SortInt{{}}}}({X}, {}), {}))",
            equals("1"),
            equals("1")
        ),
    );
    let first = "  rule [p]: <k> go(X) => done({X #Equals 1} #And X #And 1) ... </k>\n";
    assert_eq!(run(first, 1), stuck("done(1)"));
    assert_eq!(run(first, 2), trivial("go(2)"));
}

/// The specification `rules` (in module P), the claims `claims` (in module P-SPEC), and the
/// verdict of proving the claim labelled `claim`.
fn prove(rules: &str, claims: &str, claim: &str) -> String {
    prove_kore(
        &try_compile_spec(rules, claims).expect("the specification compiles"),
        claim,
    )
}

/// The verdict of proving the claim labelled `claim` of the compiled specification `kore`.
fn prove_kore(kore: &str, claim: &str) -> String {
    let mut backend = Backend::new(kore, "P-SPEC", BackendOptions::default()).unwrap();
    backend
        .prove(ProveRequest {
            claim: Some(format!("P-SPEC.{claim}")),
            max_depth: Some(20),
            ..ProveRequest::default()
        })
        .unwrap()
        .status
        .to_string()
}

/// A position of a claim outside its rewrites is in its left side as much as a rewrite's left
/// side is, so `P #as V` there denotes `P #And V` and is lowered like a left side's alias (and
/// read the same way in the right side, where the left side has bound both).
#[test]
fn a_claim_shared_alias_is_lowered_and_the_claim_is_proven() {
    let rules = "  syntax S ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]\n  syntax KItem ::= pair(Int, S) [symbol(pair)]\n  rule [h]: <k> pair(X, sa) => pair(X, sb) ... </k>\n";
    let claims = "  claim [s]: <k> pair(X #as Y, (sa => sb)) ... </k>\n  claim [t]: <k> pair(X #And 1, (sa => sb)) ... </k>\n";
    assert_eq!(prove(rules, claims, "s"), "proven");
    assert_eq!(prove(rules, claims, "t"), "proven");
    let kore = try_compile_spec(rules, claims).expect("the specification compiles");
    let shared = axiom(&kore, "P-SPEC.s");
    assert_eq!(
        shared
            .matches(&format!("Lblpair{{}}({}", lowered(X, "VarY:SortInt{}")))
            .count(),
        2,
        "{shared}"
    );
}

/// Nested aliases `(X #as Y) #as Z` denote the chain X ∧ Y ∧ Z, so a claim's left side holding
/// them is lowered as one: the claim reading Z in another cell is proven, its false twin is not.
#[test]
fn a_claim_nested_alias_is_lowered_as_a_chain_and_the_claim_is_proven() {
    let source = |claims: &str| {
        format!(
            "module P-SYNTAX
  imports INT-SYNTAX
  syntax S ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]
  syntax Pgm ::= pair(Int, S) [symbol(pair)]
endmodule

module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  configuration <k> $PGM:Pgm </k> <s> 0 </s>
  rule [h]: <k> pair(X, sa) => pair(X, sb) ... </k> <s> S => S +Int X </s>
endmodule

module P-SPEC
  imports P
{claims}endmodule
"
        )
    };
    let claims = "  claim [n]: <k> pair((X #as Y) #as Z, (sa => sb)) ... </k> <s> S => S +Int Z </s>\n  claim [m]: <k> pair((X #as Y) #as Z, (sa => sb)) ... </k> <s> S => S +Int Z +Int 1 </s>\n";
    let kore = try_compile_spec_source(source(claims)).expect("the specification compiles");
    assert_eq!(prove_kore(&kore, "n"), "proven");
    assert_ne!(prove_kore(&kore, "m"), "proven");
    let nested = axiom(&kore, "P-SPEC.n");
    let y = "VarY:SortInt{}";
    let z = "VarZ:SortInt{}";
    assert_contains(
        &nested,
        &format!(
            "Lblpair{{}}(\\and{{SortInt{{}}}}(\\and{{SortInt{{}}}}({X}, \\equals{{SortInt{{}}, SortInt{{}}}}({X}, {y})), \\equals{{SortInt{{}}, SortInt{{}}}}({X}, {z}))"
        ),
    );
}

/// `module P` over K-IO with the rules `rules`; `go(N)` and `wr()` are programs.
fn io_source(rules: &str) -> String {
    format!(
        "module P-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)] | wr() [symbol(wr)]
endmodule

module P
  imports P-SYNTAX
  imports INT
  imports BOOL
  imports STRING
  imports K-IO
  imports K-REFLECTION
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(IOInt) [symbol(done)] | res(IOInt, IOInt) [symbol(res)] | wdone(K) [symbol(wdone)]
  syntax IOInt ::= rd() [function, symbol(rd)]
  rule rd() => #getc(0)
  syntax IOInt ::= viaAny(Int) [symbol(viaAny)]
  rule viaAny(N) => #getc(N) [anywhere]
  syntax IOInt ::= rdAny() [function, symbol(rdAny)]
  rule rdAny() => viaAny(0)
  syntax IOInt ::= myGetc(Int) [function, hook(IO.getc), symbol(myGetc)]
  rule <k> done(V:Int) => res(V, #getc(0)) ... </k>
{rules}endmodule
"
    )
}

/// An operand that applies an effectful production (`impure`, or hooked to an effect such as
/// `IO.getc` without that attribute), directly or through the equations of a function, an
/// anywhere rule or a macro, performs an effect when it is evaluated: copying it into an equality would
/// duplicate the effect, and the equality is a predicate, where no effect is performed. Such a
/// conjunction is emitted as written.
#[test]
fn a_conjunction_with_an_effectful_operand_is_not_lowered() {
    for (label, conjunction) in [
        ("first", "#getc(0) #And X"),
        ("second", "X #And #getc(0)"),
        ("through", "rd() #And X"),
        ("chain", "#getc(0) #And X #And 1"),
        ("viaany", "viaAny(0) #And X"),
        ("viaanysecond", "X #And viaAny(0)"),
        ("viaanythrough", "rdAny() #And X"),
        ("unmarkedhook", "myGetc(0) #And X"),
    ] {
        let rule = format!("  rule [{label}]: <k> go(X) => done({conjunction}) ... </k>\n");
        let artifacts = compile_source(io_source(&rule), CompilationBackend::Rust);
        assert_lacks(
            &axiom(&artifacts.definition_kore, &format!("P.{label}")),
            "\\equals{",
        );
    }
    let rule = "  rule [w]: <k> wr() => wdone(#write(1, \"x\") #And .K) ... </k>\n";
    let artifacts = compile_source(io_source(rule), CompilationBackend::Rust);
    assert_lacks(&axiom(&artifacts.definition_kore, "P.w"), "\\equals{");
}

/// `krust krun --io on` of `program` over `io_source(rules)`, standard input `input`: the exit
/// status, standard output and standard error.
#[cfg(feature = "cli")]
fn krun_io(rules: &str, program: &str, input: &str, output: &[&str]) -> (i32, String, String) {
    use std::io::Write;
    use std::process::{Command, Stdio};
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let nonce = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!(
        "k-rust-ml-conditions-io-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let file = root.join("io.k");
    std::fs::write(&file, io_source(rules)).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            file.to_str().unwrap(),
            "-m",
            "P",
            "--syntax-module",
            "P-SYNTAX",
        ])
        .args(["--sort", "Pgm", "-e", program, "--io", "on"])
        .args(output)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let result = child.wait_with_output().unwrap();
    let _ = std::fs::remove_dir_all(&root);
    (
        result.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&result.stdout).into_owned(),
        String::from_utf8_lossy(&result.stderr).into_owned(),
    )
}

/// Under `--io on`, the conjunction of a read and the value it must equal reads once: 97 = 97
/// with "abc" on standard input, then the next character is 98. A write in a conjunction is
/// performed once.
#[cfg(feature = "cli")]
#[test]
fn an_effectful_conjunction_runs_its_effect_once_under_io() {
    for conjunction in [
        "#getc(0) #And X",
        "X #And #getc(0)",
        "viaAny(0) #And X",
        "X #And viaAny(0)",
        "rdAny() #And X",
        "myGetc(0) #And X",
    ] {
        let rule = format!("  rule <k> go(X) => done({conjunction}) ... </k>\n");
        let (status, stdout, stderr) = krun_io(&rule, "go(97)", "abc", &[]);
        assert_eq!(status, 0, "{conjunction}: {stderr}");
        let read = |value: &str| {
            format!("inj{{SortInt{{}},SortIOInt{{}}}}(\\dv{{SortInt{{}}}}(\"{value}\"))")
        };
        assert!(
            stdout
                .split_whitespace()
                .collect::<String>()
                .contains(&format!("Lblres{{}}({},{})", read("97"), read("98"))),
            "{conjunction}: {stdout}\n{stderr}"
        );
    }
    let rule = "  rule <k> wr() => wdone(#write(1, \"x\") #And .K) ... </k>\n";
    let (status, stdout, stderr) = krun_io(rule, "wr()", "", &["--output", "none"]);
    assert_eq!((status, stdout.as_str()), (0, "x"), "{stderr}");
}

// ---------------------------------------------------------------- shapes with no model, or no read meaning

/// The errors `kcompile` gives `sentences` for `backend` (code, line, message), or `Ok` when it
/// compiles.
fn compile_errors(
    sentences: &str,
    backend: CompilationBackend,
) -> Result<(), Vec<(String, Option<u32>, String)>> {
    source_compile_errors(format!("{HEADER}{sentences}endmodule\n"), backend)
}

/// The errors `kcompile` gives the whole definition `source` (main module `P`, syntax module
/// `P-SYNTAX`) for `backend`, as [`compile_errors`] gives them.
fn source_compile_errors(
    source: String,
    backend: CompilationBackend,
) -> Result<(), Vec<(String, Option<u32>, String)>> {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let options = LoadOptions {
        implicit_sources: vec![
            embedded("kast.md").unwrap(),
            embedded("prelude.md").unwrap(),
        ],
        ..backend.load_options()
    };
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("ml_conditions.k", source),
        "P",
        Some("P-SYNTAX"),
        &mut resolver,
        &options,
    )
    .expect("the definition loads");
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
    .map(|_| ())
    .map_err(|error| {
        let mut errors = error
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == k_rust::diagnostic::Severity::Error)
            .map(|diagnostic| {
                (
                    diagnostic.code.as_str().to_owned(),
                    diagnostic.location.map(|location| location.start_line),
                    diagnostic.message.clone(),
                )
            })
            .collect::<Vec<_>>();
        if errors.is_empty() {
            errors.push(("<none>".to_owned(), None, error.to_string()));
        }
        errors
    })
}

/// `sentences` is refused with one `MlConstructPosition` error at line `line`, whose message holds
/// each of `reasons`, and compiles for the LLVM target, whose output the refusal does not judge.
#[track_caller]
fn assert_ml_construct_refused(sentences: &str, line: usize, reasons: &[&str]) {
    let errors = match compile_errors(sentences, CompilationBackend::Rust) {
        Ok(()) => panic!("compiles:\n{sentences}"),
        Err(errors) => errors,
    };
    let [(code, at, message)] = errors.as_slice() else {
        panic!("{sentences}: not one error: {errors:?}");
    };
    assert_eq!(code, "MlConstructPosition", "{sentences}: {message}");
    assert_eq!(*at, Some(line as u32), "{sentences}: {message}");
    for reason in reasons {
        assert!(
            message.contains(reason),
            "{sentences}: no {reason:?} in {message}"
        );
    }
    assert_eq!(
        compile_errors(sentences, CompilationBackend::Llvm),
        Ok(()),
        "{sentences}: the LLVM target"
    );
}

#[track_caller]
fn assert_compiles(sentences: &str) {
    assert_eq!(
        compile_errors(sentences, CompilationBackend::Rust),
        Ok(()),
        "{sentences}"
    );
}

/// An or-pattern in the left side of a function or anywhere equation whose alternatives bind
/// different variables, one of which the result uses: the alternative that does not bind it
/// states the application's value for every value of the variable (`f(X #Or 2) => 10 +Int X`
/// states f(2) = 10 +Int X for every X), while an application has at most one value, so the
/// equation is an axiom with no model, and no answer derived from it is right.
#[test]
fn an_or_pattern_binding_a_result_variable_in_one_alternative_of_an_equation_is_refused() {
    let reasons = [
        "uses X, which the alternative",
        "does not bind",
        "or-pattern",
        "has at most one value",
        "no model",
    ];
    let first = line_after(F);
    // The message names the part of the result that uses the variable and an alternative that
    // does not bind it.
    assert_ml_construct_refused(
        &format!("{F}  rule [p]: f(X #Or 2) => 10 +Int X\n{G}"),
        first,
        &["the right side uses X, which the alternative `2` of an or-pattern"],
    );
    assert_ml_construct_refused(
        &format!("{F}  rule [p]: f(X #Or 2) => 0 ensures X >Int 0\n{G}"),
        first,
        &["the ensures uses X, which the alternative `2` of an or-pattern"],
    );
    for (sentences, line) in [
        (
            format!("{F}  rule [p]: f(X #Or 2) => 10 +Int X\n  rule [o]: f(_) => 0 [owise]\n{G}"),
            first,
        ),
        (format!("{F}  rule [p]: f(2 #Or X) => X\n{G}"), first),
        // The rule is syntactic: the right side uses X, although its value does not depend on it.
        (format!("{F}  rule [p]: f(X #Or 0) => X *Int 0\n{G}"), first),
        // No or-pattern binds X in all its alternatives: the combination f2(1, 2) binds nothing.
        (
            "  syntax Int ::= f2(Int, Int) [function, symbol(f2)]\n  rule [p]: f2(X #Or 1, X #Or 2) => X\n  rule [g]: <k> go(X) => done(f2(X, X)) ... </k>\n".to_owned(),
            line_after("  syntax Int ::= f2(Int, Int) [function, symbol(f2)]\n"),
        ),
        (
            format!("{F}  rule [p]: f(X #Or 2) => 0 ensures X >Int 0\n{G}"),
            first,
        ),
        (
            format!("{F}  rule [p]: f((X #Or 2) #Or 3) => X\n{G}"),
            first,
        ),
        (
            format!(
                "{F}  rule [p]: f(X) => 0 requires X <Int 0\n  rule [o]: f(X #Or 2) => X [owise]\n{G}"
            ),
            first + 1,
        ),
    ] {
        assert_ml_construct_refused(&sentences, line, &reasons);
    }
    let anywhere = "  syntax Wrap ::= h(Int) [symbol(h)] | w(Int) [symbol(w)]\n";
    assert_ml_construct_refused(
        &format!(
            "{anywhere}  rule [p]: h(X #Or 2) => w(X) [anywhere]\n  rule [g]: <k> go(X) => h(X) ... </k>\n"
        ),
        line_after(anywhere),
        &reasons,
    );
}

/// An or-pattern whose alternatives bind the same variables, or whose differing variables the
/// equation uses nowhere else, states one value per application; a rewrite rule matches each
/// alternative with its own bindings, as before.
#[test]
fn or_patterns_with_equal_or_unused_binders_compile() {
    for sentences in [
        format!("{F}  rule [p]: f(1 #Or 2) => 10\n{G}"),
        format!("{F}  rule [p]: f(_X #Or 2) => 0\n{G}"),
        format!("{F}  rule [p]: f(X #Or 2) => 0 requires X >Int 0 orBool true\n{G}"),
        "  syntax Int ::= f2(Int, Int) [function, symbol(f2)]\n  rule [p]: f2(X #Or 2, X) => X\n  rule [g]: <k> go(X) => done(f2(X, X)) ... </k>\n".to_owned(),
        "  rule [p]: <k> go(X #Or 2) => done(X) ... </k>\n".to_owned(),
    ] {
        assert_compiles(&sentences);
    }
    // Alternatives of different or-patterns combine independently: X is bound in every
    // alternative of the first, so in every combination, and the equation has a model.
    let combined = "  syntax W ::= g(Int) [symbol(g)] | h(Int) [symbol(h)]\n  syntax Int ::= f3(W, Int) [function, symbol(f3)]\n  rule [p]: f3(g(X) #Or h(X), X #Or 0) => X\n  rule [r]: <k> go(N) => done(f3(g(N), 0) +Int f3(h(N), N) *Int 100) ... </k>\n";
    assert_compiles(combined);
    assert_eq!(run(combined, 5), stuck("done(505)"));
}

/// A simplification whose left side is a term gives the term's value; a right side that is
/// `#Top` (every value) or only a predicate (every value or none) states that the application,
/// which has at most one value, is every value, an axiom with no model.
#[test]
fn a_simplification_of_a_term_to_top_is_refused() {
    let reasons = [
        "simplification",
        "#Top",
        "has at most one value",
        "no model",
    ];
    for sentences in [
        format!("{F}  rule [p]: f(X) => #Top [simplification]\n{G}"),
        format!("{F}  rule [p]: f(X) => #Top ensures X >Int 0 [simplification]\n{G}"),
        format!("{F}  rule [p]: f(X) +Int 1 => #Top [simplification]\n{G}"),
    ] {
        assert_ml_construct_refused(&sentences, line_after(F), &reasons);
    }
    for sentences in [
        format!("{F}  rule [p]: #Ceil(f(X)) => #Top [simplification]\n{G}"),
        format!("{F}  rule [p]: {{f(X) #Equals 1}} => #Top [simplification]\n{G}"),
        format!("{F}  rule [p]: f(X) => #Bottom [simplification]\n{G}"),
        format!("{F}  rule [p]: f(X) => X [simplification]\n{G}"),
    ] {
        assert_compiles(&sentences);
    }
}

/// A built conjunction whose operand holds a connective (`(X #Or 0) #And 1`) is left without a
/// read meaning: the lowering that gives a conjunction of two terms its meaning applies to
/// connective-free operands only, and the backend gives a built conjunction of terms no
/// definedness or value. A conjunction of a term with a predicate keeps its reading.
#[test]
fn a_built_conjunction_whose_operand_holds_a_connective_is_refused() {
    let reasons = ["#And", "connective", "conjunction"];
    for (prefix, sentences) in [
        (
            "",
            "  rule [p]: <k> go(X) => done((X #Or 0) #And 1) ... </k>\n".to_owned(),
        ),
        (
            "",
            "  rule [p]: <k> go(X) => done(1 #And (X #Or 0)) ... </k>\n".to_owned(),
        ),
        (
            "",
            "  rule [p]: <k> go(X) => done(X #And 1 #And (X #Or 2)) ... </k>\n".to_owned(),
        ),
        (F, format!("{F}  rule [p]: f(X) => (X #Or 0) #And 1\n{G}")),
    ] {
        assert_ml_construct_refused(&sentences, line_after(prefix), &reasons);
    }
    for sentences in [
        "  rule [p]: <k> go(X) => done((X #Or 0) #And {X #Equals 1}) ... </k>\n",
        "  rule [p]: <k> go(X) => done(X #And 1) ... </k>\n",
        "  rule [p]: <k> go(X) => done(X #Or 0) ... </k>\n",
        "  rule [p]: <k> go(X #And 1) => done(X) ... </k>\n",
        // A conjunction of terms without a connective, and a term conjoined with a predicate,
        // are at most one value each, so the outer conjunction is one of single-valued terms.
        "  syntax W ::= g(Int) [symbol(g)]\n  syntax KItem ::= dw(W) [symbol(dw)]\n  rule [p]: <k> go(X) => dw(g(X #And 1) #And g(1)) ... </k>\n",
        "  syntax W ::= g(Int) [symbol(g)]\n  syntax KItem ::= dw(W) [symbol(dw)]\n  rule [p]: <k> go(X) => dw(g(X #And {X #Equals 1}) #And g(1)) ... </k>\n",
    ] {
        assert_compiles(sentences);
    }
}

/// `#if`, `andThenBool` and `orElseBool` are strict: an undefined operand makes them undefined
/// whichever operand they select, so a term conjunction in an operand they discard still states
/// the equality of its operands.
#[test]
fn a_term_conjunction_in_a_discarded_operand_constrains_definedness() {
    // `#if` is declared in K-EQUAL.
    let run = |condition: &str, n: i64| {
        let source = format!(
            "{}  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\nendmodule\n",
            HEADER.replace("  imports BOOL\n", "  imports BOOL\n  imports K-EQUAL\n")
        );
        let kore = compile_source(source, CompilationBackend::Rust).definition_kore;
        run_kore_states(&kore, n)
            .into_iter()
            .map(|(reason, k, _)| (reason, k))
            .collect::<Vec<_>>()
    };
    for condition in [
        "#Ceil(#if X ==Int 1 #then 0 #else (X #And 5) #fi)",
        "#Ceil(false andThenBool ((X #And 5) ==Int 1))",
        "#Ceil(true orElseBool ((X #And 5) ==Int 1))",
    ] {
        assert_eq!(run(condition, 1), stuck("go(1)"), "{condition}");
        assert_eq!(run(condition, 3), stuck("go(3)"), "{condition}");
        assert_eq!(run(condition, 5), stuck("done(5)"), "{condition}");
    }
}

/// `#Ceil(t1 #And t2)` of two terms, each at most one value, holds exactly where t1 is defined
/// and equals t2: a condition that reads it so steps where it holds and only there, as a
/// definedness atom below an application or under `#Not` does.
#[test]
fn the_definedness_of_a_term_conjunction_is_the_equality_of_its_operands() {
    let rule = |condition: &str| {
        format!("  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n")
    };
    for condition in [
        "#Ceil(X #And 1)",
        "#Ceil(1 #And X)",
        "#Ceil(X #And 1 #And X)",
        "#Ceil((X +Int 0) #And 1)",
    ] {
        assert_eq!(run(&rule(condition), 1), stuck("done(1)"), "{condition}");
        assert_eq!(run(&rule(condition), 3), stuck("go(3)"), "{condition}");
    }
    let negated = rule("#Not(#Ceil(X #And 1))");
    assert_eq!(run(&negated, 1), stuck("go(1)"));
    assert_eq!(run(&negated, 3), stuck("done(3)"));
    // In a function equation's requires, the application is evaluated where it holds.
    let equation = format!(
        "{F}  rule [p]: f(X) => X requires #Ceil(X #And 1)\n  rule [o]: f(_) => 0 [owise]\n{G}"
    );
    assert_eq!(run(&equation, 1), stuck("done(1)"));
    assert_eq!(run(&equation, 3), stuck("done(0)"));
}

// ---------------------------------------------------------------- positions, after macro expansion

const IS_P: &str = "  syntax Bool ::= isP(Int) [macro]\n  rule isP(X) => {X #Equals 1}\n";

/// A macro is an abbreviation: what its body states is judged where it is used, in the context of
/// the use. `isP(X)`, which expands to the predicate `{X #Equals 1}`, is a condition at the root of
/// a requires, and a predicate where a Bool value is required below `notBool`.
#[test]
fn a_predicate_macro_is_judged_in_the_context_of_its_use() {
    let rule = |condition: &str| {
        format!("{IS_P}  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n")
    };
    assert_eq!(run(&rule("isP(X)"), 1), stuck("done(1)"));
    assert_eq!(run(&rule("isP(X)"), 3), stuck("go(3)"));
    assert_ml_construct_refused(
        &rule("notBool isP(X)"),
        line_after(IS_P),
        &[
            "#Equals (written in the body of a macro or alias used here)",
            "below a Bool symbol",
            "a predicate where a Bool value is required",
        ],
    );
}

/// Shapes every route reads at the base keep compiling: or-patterns whose alternatives bind
/// different variables in a rewrite rule's left side or at a shared position, `#Top` (any value)
/// and `#Bottom` (no value) at a shared position, and an or-pattern with unequal binders in a
/// claim's left side.
#[test]
fn matched_and_shared_shapes_that_work_keep_compiling() {
    for sentences in [
        "  rule [p]: <k> go(X #Or 2) => done(X) ... </k>\n",
        "  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]\n  syntax KItem ::= pair(Int, Step) [symbol(pair)]\n  rule [p]: <k> pair(X #Or 2, (sa => sb)) ... </k>\n",
        "  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]\n  syntax KItem ::= pair(Int, Step) [symbol(pair)]\n  rule [p]: <k> pair(#Top, (sa => sb)) ... </k>\n",
        "  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]\n  syntax KItem ::= pair(Int, Step) [symbol(pair)]\n  rule [p]: <k> pair(#Bottom, (sa => sb)) ... </k>\n",
        "  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]\n  syntax KItem ::= pair(Int, Step) [symbol(pair)]\n  rule [p]: <k> pair({1 #Equals 1}, (sa => sb)) ... </k>\n",
    ] {
        assert_compiles(sentences);
    }
    try_compile_spec(
        "  rule [g]: <k> go(X) => done(X) ... </k> requires X <Int 3\n",
        "  claim [p]: <k> go(X #Or 2) => done(?_) ... </k>\n",
    )
    .expect("a claim's or-pattern with unequal binders compiles");
}

/// One shape of each context the check refuses, refused at compile with a located diagnostic for
/// the Rust target, and compiled as before for the LLVM target, whose consumer reads the emitted
/// KORE on its own terms.
const REFUSED_SHAPES: &[(&str, &str)] = &[
    (
        "  rule [p]: <k> go(X) => done(X) ... </k> requires notBool {X #Equals 3}\n",
        "below a Bool symbol",
    ),
    (
        "  rule [p]: <k> go(X) => done(#Not(X)) ... </k>\n",
        "where the rewrite rule builds its result",
    ),
    (
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {X #Equals (1 #Or 2) +Int 0}\n",
        "inside an operand of #Equals",
    ),
    (
        "  rule [p]: <k> go(3 #Implies 4) => done(0) ... </k>\n",
        "where the rewrite rule matches",
    ),
    (
        "  rule [p]: <k> go(X) => done(X) ... </k> requires { {{X #Equals 1} #Equals true} #Equals #Top }\n",
        "whose operands are not both terms",
    ),
];

#[test]
fn each_refused_context_is_located_and_the_llvm_target_compiles_it() {
    for (sentences, reason) in REFUSED_SHAPES {
        assert_ml_construct_refused(sentences, line_after(""), &[reason]);
    }
}

/// The structured route (`load_structured`, which a client that builds sentences itself takes)
/// reaches the same check: the same shapes give the same located diagnostic.
#[test]
fn the_structured_route_refuses_the_same_shapes() {
    for (sentences, reason) in &REFUSED_SHAPES[..3] {
        let source = format!("{HEADER}{sentences}endmodule\n");
        let definition = k_rust::outer::lower(
            &k_rust::outer::parse("ml_conditions.k", &source).expect("the definition parses"),
            "P",
        )
        .expect("the definition lowers");
        let options = LoadOptions {
            implicit_sources: vec![
                embedded("kast.md").unwrap(),
                embedded("prelude.md").unwrap(),
            ],
            ..CompilationBackend::Rust.load_options()
        };
        let loaded = k_rust::outer::load_structured(definition, &options)
            .expect("the structured definition loads");
        let error = compile_loaded_definition(&loaded, CompileOptions::default())
            .expect_err("the structured definition is refused");
        let diagnostic = error
            .diagnostics
            .iter()
            .find(|diagnostic| diagnostic.code.as_str() == "MlConstructPosition")
            .unwrap_or_else(|| panic!("{sentences}: no MlConstructPosition in {error}"));
        assert!(
            diagnostic.message.contains(reason),
            "{sentences}: no {reason:?} in {}",
            diagnostic.message
        );
        assert!(diagnostic.location.is_some(), "{sentences}: unlocated");
    }
}

/// A function equation written with the configuration (`[[ f(..) => r ]] <cells>`) defines the
/// same application: an or-pattern at the root of one of its arguments is matched, as in an
/// equation without the configuration, and one below a symbol of an argument is refused.
#[test]
fn an_or_pattern_of_a_function_equation_with_the_configuration_is_judged_at_its_arguments() {
    let declarations = "  syntax Reason ::= \"ra\" [symbol(ra)] | \"rb\" [symbol(rb)] | \"rc\" [symbol(rc)] | w(Reason) [symbol(w)]\n  syntax Int ::= cw(Reason) [function, total, symbol(cw)] | cv(Reason) [function, total, symbol(cv)]\n  rule cw(_) => 0 [owise]\n  rule cv(_) => 0 [owise]\n";
    assert_compiles(&format!(
        "{declarations}  rule [p]: [[ cw(ra #Or rb) => 1 ]] <k> _ </k>\n"
    ));
    assert_ml_construct_refused(
        &format!("{declarations}  rule [p]: [[ cv(w(ra #Or rb)) => 1 ]] <k> _ </k>\n"),
        line_after(declarations),
        &["matched only at the root of an argument"],
    );
}

// ---------------------------------------------------------------- MLP/4b fix round 1

/// The rule every claim below is proved against.
const GO_DONE: &str = "  rule [g]: <k> go(X) => done(X) ... </k>\n";

/// The line of the first claim of `try_compile_spec(rules, claims)`.
fn claim_line(rules: &str) -> usize {
    HEADER.lines().count() + rules.lines().count() + 5
}

/// A claim's right side is the pattern every path must reach. `P #as V` there denotes `P #And V`,
/// which is `P #And {P #Equals V}` where `P` denotes at most one value and evaluating it performs
/// no effect, the form `lower term conjunctions` writes. Where `P` holds a connective or applies
/// an effectful production, that form does not denote the alias, and no other compiled form
/// keeps `P`: the claim is refused at compile, for every target, rather than proved against a
/// right side that lost `P` (`(done(X +Int 1) #Or done(7)) #as ?Y` would become `?Y`, which
/// every state matches).
#[test]
fn a_claim_right_side_alias_that_is_not_lowered_is_refused() {
    let effectful =
        "  syntax Int ::= eff(Int) [function, impure, symbol(eff)]\n  rule eff(X) => X\n";
    // The LLVM target's definition checks also refuse a claim's existential variables
    // (UnsupportedExistentialVariable). The rewrite checks refuse the aliases with a connective
    // beside that; the effects of an alias's pattern are judged by a later stage, so the
    // effectful claim is refused there by that code alone.
    for (rules, claim, targets) in [
        (
            GO_DONE.to_owned(),
            "  claim [p]: <k> go(X) => (done(X +Int 1) #Or done(7)) #as ?Y </k>\n",
            2,
        ),
        (
            GO_DONE.to_owned(),
            "  claim [p]: <k> go(X) => done(((X +Int 1) #Or 7) #as ?Y) </k>\n",
            2,
        ),
        (
            GO_DONE.to_owned(),
            "  claim [p]: <k> go(X) => (done(X) #Or done(0)) #as ?Y ... </k>\n",
            2,
        ),
        (
            format!("{effectful}{GO_DONE}"),
            "  claim [p]: <k> go(X) => done(eff(X) #as ?Y) ... </k>\n",
            1,
        ),
    ] {
        for (index, backend) in [CompilationBackend::Rust, CompilationBackend::Llvm]
            .into_iter()
            .enumerate()
        {
            let source = format!(
                "{HEADER}{rules}endmodule\n\nmodule P-SPEC\n  imports P\n{claim}endmodule\n"
            );
            let message = match try_compile_spec_source_for(source, backend) {
                Ok(_) => panic!("{backend:?}: compiles:\n{claim}"),
                Err(message) => message,
            };
            if index >= targets {
                continue;
            }
            let at = format!(
                "ml_conditions.k:{}:3: MlConstructPosition: ",
                claim_line(&rules)
            );
            assert!(
                message.contains(&at),
                "{backend:?}: {claim}: not refused at {at:?}: {message}"
            );
            assert!(
                message.contains("#as") && message.contains("right-hand side"),
                "{backend:?}: {claim}: {message}"
            );
        }
    }
    // An alias of a plain term is lowered, so it compiles. (The LLVM target's checks refuse a
    // claim's existential variables, whatever their position.)
    let source = format!(
        "{HEADER}{GO_DONE}endmodule\n\nmodule P-SPEC\n  imports P\n  claim [p]: <k> go(X) => done(X #as ?Y) ... </k> ensures ?Y ==Int X\n  claim [q]: <k> go(X) => done((X #as ?Y) #as ?Z) ... </k>\nendmodule\n"
    );
    try_compile_spec_source_for(source, CompilationBackend::Rust)
        .unwrap_or_else(|error| panic!("{error}"));
}

/// `#Bottom` denotes no value, so `X #Or #Bottom` is `X`: an equation's result whose
/// alternatives other than `#Bottom` are at most one denotes at most one value, in a function, a
/// simplification and an anywhere rule, at the root of the result or below a symbol.
#[test]
fn an_equation_result_with_bottom_alternatives_compiles_and_gives_its_value() {
    for (rule, at_one) in [
        ("  rule [p]: f(X) => X #Or #Bottom\n", "done(1)"),
        ("  rule [p]: f(X) => #Bottom #Or X\n", "done(1)"),
        (
            "  rule [p]: f(X) => (X #Or #Bottom) #Or #Bottom\n",
            "done(1)",
        ),
        ("  rule [p]: f(X) => 1 +Int (X #Or #Bottom)\n", "done(2)"),
        (
            "  syntax Int ::= s(Int) [function, symbol(s)]\n  rule s(X) => X\n  rule [p]: s(X) => X #Or #Bottom [simplification]\n  rule f(X) => s(X)\n",
            "done(1)",
        ),
        (
            "  syntax KItem ::= a(Int) [symbol(a)] | h(Int) [symbol(h)]\n  rule [p]: a(X) => h(X) #Or #Bottom [anywhere]\n  rule f(X) => X\n",
            "done(1)",
        ),
    ] {
        let sentences = format!("{F}{rule}{G}");
        assert_compiles(&sentences);
        assert_eq!(run(&sentences, 1), stuck(at_one), "{rule}");
    }
    // Two alternatives that are not #Bottom still denote two values.
    assert_ml_construct_refused(
        &format!("{F}  rule [p]: f(X) => (X #Or #Bottom) #Or 1\n{G}"),
        line_after(F),
        &["a disjunction of unguarded alternatives"],
    );
}

/// An or-pattern at the root of an argument whose alternatives are of a sort below the
/// argument's is placed there by an injection, or as the item of a one-item k-sequence for an
/// argument of sort `K`: the or-pattern then stands below a symbol, where no equation reads it,
/// and the equation is refused. Alternatives of the argument's own sort keep it at the root.
#[test]
fn an_or_pattern_below_the_injection_or_the_sequence_of_an_argument_is_refused() {
    let reasons = ["#Or", "injection", "one equation per alternative"];
    let kitem = "  syntax Int ::= fi(KItem) [function, symbol(fi)]\n";
    let k = "  syntax Int ::= fk(K) [function, symbol(fk)]\n";
    let exp = "  syntax Exp ::= Int | e(Int) [symbol(e)]\n  syntax Int ::= fe(Exp) [function, symbol(fe)]\n";
    for (declarations, rule, rest) in [
        (
            kitem,
            "  rule [p]: fi(1 #Or 2) => 5\n",
            "  rule fi(_) => 0 [owise]\n  rule <k> go(X) => done(fi(X)) ... </k>\n",
        ),
        (
            k,
            "  rule [p]: fk(1 #Or 2) => 5\n",
            "  rule fk(_) => 0 [owise]\n  rule <k> go(X) => done(fk(X)) ... </k>\n",
        ),
        (
            k,
            "  rule [p]: fk(done(1) #Or done(2)) => 5\n",
            "  rule fk(_) => 0 [owise]\n  rule <k> go(X) => done(fk(done(X))) ... </k>\n",
        ),
        (
            exp,
            "  rule [p]: fe(1 #Or 2) => 5\n",
            "  rule fe(_) => 0 [owise]\n  rule <k> go(X) => done(fe(X)) ... </k>\n",
        ),
        (
            "  syntax KItem ::= a(KItem) [symbol(a)]\n",
            "  rule [p]: a(1 #Or 2) => done(5) [anywhere]\n",
            "  rule <k> go(X) => a(X) ... </k>\n",
        ),
    ] {
        assert_ml_construct_refused(
            &format!("{declarations}{rule}{rest}"),
            line_after(declarations),
            &reasons,
        );
    }
    // The or-pattern is at the argument's sort: the alternatives are of that sort, or of two
    // sorts whose join it is.
    for (declarations, rules, (one, three)) in [
        (
            kitem,
            "  rule fi(done(1) #Or done(2)) => 5\n  rule fi(_) => 0 [owise]\n  rule <k> go(X) => done(fi(done(X))) ... </k>\n",
            ("done(5)", "done(0)"),
        ),
        (
            kitem,
            "  rule fi(1 #Or done(2)) => 5\n  rule fi(_) => 0 [owise]\n  rule <k> go(X) => done(fi(X)) ... </k>\n",
            ("done(5)", "done(0)"),
        ),
        (
            kitem,
            "  rule fi(I:Int #Or done(I:Int)) => I\n  rule fi(_) => 0 [owise]\n  rule <k> go(X) => done(fi(X)) ... </k>\n",
            ("done(1)", "done(3)"),
        ),
        (
            exp,
            "  rule fe(1 #Or e(2)) => 5\n  rule fe(_) => 0 [owise]\n  rule <k> go(X) => done(fe(X)) ... </k>\n",
            ("done(5)", "done(0)"),
        ),
    ] {
        let sentences = format!("{declarations}{rules}");
        assert_compiles(&sentences);
        assert_eq!(run(&sentences, 1), stuck(one), "{rules}");
        assert_eq!(run(&sentences, 3), stuck(three), "{rules}");
    }
}

/// A `#Top`, a `#Bottom` or a predicate at a position the sides of a rewrite rule share is read
/// as the value it names only where that position is itself what the two sides share: an
/// argument of a symbol whose other arguments hold the rewrite. As part of a larger shared
/// term, or as an item of a k-sequence that holds the rewrite, it would stand below a symbol of
/// the term the rule matches, where no rule reads it, and the rule is refused.
#[test]
fn a_shared_top_bottom_or_predicate_that_is_part_of_a_larger_shared_term_is_refused() {
    let pair = "  syntax Step ::= \"sa\" [symbol(sa)] | \"sb\" [symbol(sb)]\n  syntax KItem ::= pair(Int, Step) [symbol(pair)]\n";
    for (declarations, rule, construct) in [
        (
            pair,
            "  rule [p]: <k> pair(#Top, sa) ~> (.K => done(0)) </k>\n",
            "#Top",
        ),
        (
            "",
            "  rule [p]: <k> #Top ~> (go(X) => done(X)) </k>\n",
            "#Top",
        ),
        (
            "",
            "  rule [p]: <k> (go(X) => done(X)) ~> #Top </k>\n",
            "#Top",
        ),
        (
            "",
            "  rule [p]: <k> #Top ~> (go(X) => done(X)) ... </k>\n",
            "#Top",
        ),
        (
            pair,
            "  rule [p]: <k> pair(#Bottom, sa) ~> (.K => done(0)) </k>\n",
            "#Bottom",
        ),
        (
            "",
            "  rule [p]: <k> #Bottom ~> (go(X) => done(X)) </k>\n",
            "#Bottom",
        ),
        (
            "",
            "  rule [p]: <k> {X #Equals 1} ~> (go(X) => done(X)) </k>\n",
            "#Equals",
        ),
        (
            pair,
            "  rule [p]: <k> pair({1 #Equals 1}, sa) ~> (.K => done(0)) </k>\n",
            "#Equals",
        ),
    ] {
        assert_ml_construct_refused(
            &format!("{declarations}{rule}"),
            line_after(declarations),
            &[
                construct,
                "at a position the sides of the rewrite rule share",
            ],
        );
    }
}

/// An or-pattern at the root of an argument of an equation, under `#as`, is below the alias the
/// equation matches; the remedy distributes the alias over the alternatives, which keeps them at
/// the root.
#[test]
fn an_aliased_or_pattern_at_an_argument_root_is_told_to_distribute_the_alias() {
    assert_ml_construct_refused(
        &format!("{F}  rule [p]: f((1 #Or 2) #as Y) => Y +Int 10\n{G}"),
        line_after(F),
        &["below #as", "(1 #as Y) #Or (2 #as Y)"],
    );
    let distributed = format!("{F}  rule [p]: f((1 #as Y) #Or (2 #as Y)) => Y +Int 10\n{G}");
    assert_compiles(&distributed);
    assert_eq!(run(&distributed, 1), stuck("done(11)"));
    assert_eq!(run(&distributed, 2), stuck("done(12)"));
}

// ---------------------------------------------------------------- search-pattern conditions

/// Three rules from `go(0)`, to `done(1)`, `done(2)` and `done(3)`: the final states a search
/// pattern over `done(X)` selects from.
const BRANCHES: &str = "  rule [s1]: <k> go(0) => done(1) ... </k>\n  rule [s2]: <k> go(0) => done(2) ... </k>\n  rule [s3]: <k> go(0) => done(3) ... </k>\n";

/// Search patterns whose condition is a plain Bool term (or none), each with its compiled KORE
/// at the base of the ticket that reads search-pattern conditions as predicates: a Bool term is
/// one leaf, as before.
const PLAIN_BOOL_PATTERNS: &[(&str, &str)] = &[
    (
        "<k> done(X) </k>",
        r#"\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbldone{}(VarX:SortInt{}), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \equals{SortBool{}, SortGeneratedTopCell{}}(LblisInt{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarX:SortInt{}), dotk{}())), \dv{SortBool{}}("true")))"#,
    ),
    (
        "<k> done(X) </k> requires X <Int 3",
        r#"\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbldone{}(VarX:SortInt{}), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'Unds'andBool'Unds'{}(LblisInt{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarX:SortInt{}), dotk{}())), Lbl'Unds-LT-'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("3"))), \dv{SortBool{}}("true")))"#,
    ),
    (
        "<k> done(X) </k> requires X >Int 0 andBool notBool (X ==Int 2)",
        r#"\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbldone{}(VarX:SortInt{}), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'Unds'andBool'Unds'{}(LblisInt{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarX:SortInt{}), dotk{}())), Lbl'Unds'andBool'Unds'{}(Lbl'Unds-GT-'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("0")), LblnotBool'Unds'{}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("2"))))), \dv{SortBool{}}("true")))"#,
    ),
    (
        "<k> done(X:Int) ~> _ </k> requires X <Int 3",
        r#"\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbldone{}(VarX:SortInt{}), Var'Unds'Gen0:SortK{})), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'Unds'andBool'Unds'{}(Lbl'Unds'andBool'Unds'{}(LblisInt{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarX:SortInt{}), dotk{}())), LblisK{}(Var'Unds'Gen0:SortK{})), Lbl'Unds-LT-'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("3"))), \dv{SortBool{}}("true")))"#,
    ),
    (
        "<k> done(X) ~> K:KItem </k> requires X <Int 3",
        r#"\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbldone{}(VarX:SortInt{}), kseq{}(VarK:SortKItem{}, dotk{}()))), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'Unds'andBool'Unds'{}(Lbl'Unds'andBool'Unds'{}(LblisInt{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarX:SortInt{}), dotk{}())), LblisKItem{}(kseq{}(VarK:SortKItem{}, dotk{}()))), Lbl'Unds-LT-'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("3"))), \dv{SortBool{}}("true")))"#,
    ),
    (
        "<k> done(X) </k> requires isOne(X) orBool X ==Int 3",
        r#"\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(Lbldone{}(VarX:SortInt{}), dotk{}())), Var'Unds'DotVar0:SortGeneratedCounterCell{}), \equals{SortBool{}, SortGeneratedTopCell{}}(Lbl'Unds'andBool'Unds'{}(LblisInt{}(kseq{}(inj{SortInt{}, SortKItem{}}(VarX:SortInt{}), dotk{}())), Lbl'Unds'orBool'Unds'{}(LblisOne{}(VarX:SortInt{}), Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{}, \dv{SortInt{}}("3")))), \dv{SortBool{}}("true")))"#,
    ),
];

/// A search pattern whose condition is a plain Bool term compiles to the KORE it compiled to
/// before search-pattern conditions were read as predicates: the condition is one leaf
/// `\equals{SortBool{}, SortGeneratedTopCell{}}(t, true)`.
#[test]
fn a_plain_bool_search_pattern_condition_compiles_as_before() {
    let sentences = format!(
        "{BRANCHES}  syntax Bool ::= isOne(Int) [function, total, symbol(isOne)]\n  rule isOne(N) => N ==Int 1\n"
    );
    for (pattern, expected) in PLAIN_BOOL_PATTERNS {
        assert_eq!(compile_pattern(&sentences, pattern), *expected, "{pattern}");
    }
}

/// A search pattern's condition is a predicate over the match, as a rule's condition is: each
/// matching-logic connective at its root is a predicate connective at the pattern's sort, and
/// each atom keeps its operand sort.
#[test]
fn a_search_pattern_condition_is_the_predicate_it_states() {
    let pattern = compile_pattern(BRANCHES, "<k> done(X) </k> requires {X #Equals 1}");
    assert_contains(&pattern, &x_equals(TOP, "1"));
    assert_lacks(
        &pattern,
        &format!("\\equals{{SortBool{{}}, {TOP}}}(\\equals"),
    );
    let pattern = compile_pattern(
        BRANCHES,
        "<k> done(X) </k> requires (X ==Int 1) #Or {X #Equals 2}",
    );
    assert_contains(
        &pattern,
        &format!(
            "\\or{{{TOP}}}({}, {})",
            leaf(TOP, &eq_int(X, &int("1"))),
            x_equals(TOP, "2")
        ),
    );
    assert_no_bool_connective(&pattern);
}

/// The error of a search pattern refused at compile: its code and line.
#[track_caller]
fn pattern_refusal(source: String, contents: &str) -> (String, Option<u32>, String) {
    match try_compile_pattern_source(source, contents) {
        Ok(pattern) => panic!(
            "{contents} compiles: {}",
            Printer::compact().print_pattern(&pattern)
        ),
        Err(CompileSearchPatternError::Denotation(diagnostic)) => (
            diagnostic.code.as_str().to_owned(),
            diagnostic.location.map(|location| location.start_line),
            diagnostic.message.clone(),
        ),
        Err(error) => panic!("{contents}: refused without a diagnostic: {error}"),
    }
}

/// A construct a search pattern states no meaning with is refused at compile, located at the
/// pattern, with the code the route gives its refusals: a predicate below a Bool symbol, a
/// connective inside a predicate operand, a local function (which the route does not lower), and
/// a predicate where the pattern's body is matched.
#[test]
fn a_search_pattern_construct_with_no_reading_is_refused_where_it_is_written() {
    for (contents, reason) in [
        (
            "<k> done(X) </k> requires notBool {X #Equals 3}",
            "where a Bool value is required",
        ),
        (
            "<k> done(X) </k> requires (X #Or 5) <Int 3",
            "where a Bool value is required",
        ),
        (
            "<k> done(X) </k> requires #Ceil(X #Or 1)",
            "inside an operand of #Equals, #Ceil or #Floor",
        ),
        (
            "<k> done(X) </k> requires {X #Equals (1 #Or 2)}",
            "whose operands are not both terms",
        ),
        (
            "<k> done(X) </k> requires #let Z = X #in (Z ==Int 1)",
            "local function",
        ),
        ("<k> done(#Top) </k>", "where the search pattern matches"),
    ] {
        let (code, line, message) =
            pattern_refusal(format!("{HEADER}{BRANCHES}endmodule\n"), contents);
        assert_eq!(
            (code.as_str(), line),
            ("InvalidSearchPattern", Some(1)),
            "{contents}: {message}"
        );
        assert!(message.contains(reason), "{contents}: {message}");
    }
}

/// The variables a KORE pattern binds, and those that occur free in it.
fn bound_and_free(pattern: &Pattern) -> (Vec<String>, std::collections::BTreeSet<String>) {
    fn walk(
        pattern: &Pattern,
        scope: &mut Vec<String>,
        bound: &mut Vec<String>,
        free: &mut std::collections::BTreeSet<String>,
    ) {
        match pattern {
            Pattern::Variable(variable) => {
                if !scope.contains(&variable.name) {
                    free.insert(variable.name.clone());
                }
            }
            Pattern::Exists { variable, body, .. } | Pattern::Forall { variable, body, .. } => {
                bound.push(variable.name.clone());
                scope.push(variable.name.clone());
                walk(body, scope, bound, free);
                scope.pop();
            }
            Pattern::Application { arguments, .. }
            | Pattern::And { arguments, .. }
            | Pattern::Or { arguments, .. }
            | Pattern::AssociativeApplication { arguments, .. } => {
                for argument in arguments {
                    walk(argument, scope, bound, free);
                }
            }
            Pattern::Not { argument, .. }
            | Pattern::Next { argument, .. }
            | Pattern::Ceil { argument, .. }
            | Pattern::Floor { argument, .. } => walk(argument, scope, bound, free),
            Pattern::Implies { left, right, .. }
            | Pattern::Iff { left, right, .. }
            | Pattern::Rewrites { left, right, .. }
            | Pattern::Equals { left, right, .. }
            | Pattern::In { left, right, .. } => {
                walk(left, scope, bound, free);
                walk(right, scope, bound, free);
            }
            Pattern::Mu { variable, body } | Pattern::Nu { variable, body } => {
                bound.push(variable.name.clone());
                scope.push(variable.name.clone());
                walk(body, scope, bound, free);
                scope.pop();
            }
            Pattern::String(_)
            | Pattern::Top { .. }
            | Pattern::Bottom { .. }
            | Pattern::DomainValue { .. } => {}
        }
    }
    let (mut scope, mut bound, mut free) = (Vec::new(), Vec::new(), Default::default());
    walk(pattern, &mut scope, &mut bound, &mut free);
    (bound, free)
}

/// A binder's sort annotation in a search pattern restricts the bound variable, so the sort test
/// a cast of it adds belongs inside the binder's scope: the compiled pattern binds each name once
/// and never names a bound variable outside its binder (bound-name uniqueness). Where the
/// binder's own sort is the cast's sort the test is implied and dropped; otherwise it is
/// conjoined inside the binder.
#[test]
fn a_search_pattern_binder_s_sort_test_stays_in_its_scope() {
    for contents in [
        "<k> done(X) </k> requires #Exists Y:Int . {X #Equals Y}",
        "<k> done(X) </k> requires #Exists Y . {X #Equals Y:Int}",
        "<k> done(X) </k> requires #Forall Y:Int . ((Y ==Int X) impliesBool (Y <Int 3))",
        "<k> done(X) </k> requires #Exists Y:Int . #Exists Z:Int . {X #Equals Y +Int Z}",
        "<k> done(X) </k> requires (#Exists Y:Int . {X #Equals Y}) #And (X <Int 3)",
        "<k> done(X) ~> K:KItem </k> requires #Exists Y . ({X #Equals Y:Int} #And {K #Equals Y:KItem})",
        "<k> done(X) ~> K:KItem </k> requires #Exists Y:Int . {X #Equals Y}",
    ] {
        let pattern =
            try_compile_pattern_source(format!("{HEADER}{BRANCHES}endmodule\n"), contents)
                .unwrap_or_else(|error| panic!("{contents}: {error}"));
        let (bound, free) = bound_and_free(&pattern);
        let printed = Printer::compact().print_pattern(&pattern);
        assert!(!bound.is_empty(), "{contents}: binds nothing: {printed}");
        let unique = bound.iter().collect::<std::collections::BTreeSet<_>>();
        assert_eq!(unique.len(), bound.len(), "{contents}: {printed}");
        for name in &bound {
            assert!(
                !free.contains(name),
                "{contents}: the bound {name} occurs free: {printed}"
            );
        }
    }
}

/// `krust krun --pattern` of the definition `sentences` from `go(0)`, searching final states at
/// depth at most 5: the exit status, standard output and standard error.
#[cfg(feature = "cli")]
fn krun_pattern(sentences: &str, pattern: &str) -> (i32, String, String) {
    use std::process::{Command, Stdio};
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let nonce = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let root = std::env::temp_dir().join(format!(
        "k-rust-ml-conditions-pattern-{}-{nonce}",
        std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();
    let file = root.join("search.k");
    std::fs::write(&file, format!("{HEADER}{sentences}endmodule\n")).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_krust"))
        .args([
            "krun",
            file.to_str().unwrap(),
            "-m",
            "P",
            "--syntax-module",
            "P-SYNTAX",
        ])
        .args([
            "--sort",
            "Pgm",
            "-e",
            "go(0)",
            "--search-final",
            "--depth",
            "5",
        ])
        .args(["--pattern", pattern])
        .stdin(Stdio::null())
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&root);
    (
        result.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&result.stdout).into_owned(),
        String::from_utf8_lossy(&result.stderr).into_owned(),
    )
}

/// `krust krun --pattern` with a predicate condition finds the final states the condition admits.
#[cfg(feature = "cli")]
#[test]
fn krun_pattern_with_a_predicate_condition_finds_the_states_it_admits() {
    let found = |value: &str| {
        format!(
            "\\equals{{SortInt{{}},SortGeneratedTopCell{{}}}}(VarX:SortInt{{}},\\dv{{SortInt{{}}}}(\"{value}\"))"
        )
    };
    for (condition, expected) in [
        ("{X #Equals 1}", found("1")),
        (
            "{X #Equals 1} #Or {X #Equals 2}",
            format!(
                "\\or{{SortGeneratedTopCell{{}}}}({},{})",
                found("1"),
                found("2")
            ),
        ),
        (
            "#Not({X #Equals 3})",
            format!(
                "\\or{{SortGeneratedTopCell{{}}}}({},{})",
                found("1"),
                found("2")
            ),
        ),
    ] {
        let (status, stdout, stderr) =
            krun_pattern(BRANCHES, &format!("<k> done(X) </k> requires {condition}"));
        assert_eq!(status, 0, "{condition}: {stderr}");
        assert_eq!(
            stdout.split_whitespace().collect::<String>(),
            expected,
            "{condition}: {stderr}"
        );
    }
}

// ---------------------------------------------------------------- effects inside predicate operands

/// The line of the first rule `io_source` places.
fn io_line() -> usize {
    io_source("").lines().count()
}

/// `sel(0)` reads the console, and `sel(N)` is `N` elsewhere: one of its equations applies an
/// effect and the other does not.
const SEL: &str = "  syntax IOInt ::= sel(Int) [function, symbol(sel)]\n  rule sel(0) => #getc(0)\n  rule sel(N) => N requires N =/=Int 0\n";

/// The line of the sentence labelled `p` when `rules` is placed by `io_source`.
fn io_probed_line(rules: &str) -> u32 {
    let offset = rules
        .lines()
        .position(|line| line.contains("[p]"))
        .expect("a sentence labelled p");
    (io_line() + offset) as u32
}

/// A predicate states a truth value about the matched state, so an application whose value
/// certainly depends on an effect (a read of the console, a write's status, a trace, a random
/// number, the environment, the command line) has no meaning inside its operand: such an operand
/// is refused at compile, located at the sentence, directly, through a macro, or through a
/// function all of whose equations apply the effect. The LLVM target, whose output the check does
/// not judge, compiles each.
#[test]
fn an_effect_inside_a_predicate_operand_is_refused_at_compile() {
    for rule in [
        "  rule [p]: <k> go(X) => done(X #And {#getc(0) #Equals 97} #And 97) ... </k>\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#getc(0) #Equals 97}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {X #Equals 5} #Or {myGetc(0) #Equals 97}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires #Ceil(rd())\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> ensures {rdAny() #Equals 97}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#write(1, \"x\") #Equals .K}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {randInt(10) #Equals 3}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#trace(X) #Equals .K}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#traceK(X) #Equals .K}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#logToFile(\"f\", \"x\") #Equals .K}\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires #Ceil(#argv())\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#kompiledDirectory() #Equals \"\"}\n",
        "  syntax IOInt ::= mrd() [macro]\n  rule mrd() => #getc(0)\n  rule [p]: <k> go(X) => done(X) ... </k> requires {mrd() #Equals 97}\n",
        "  syntax IOInt ::= rdi() [function, impure, symbol(rdi)]\n  rule rdi() => #getc(0)\n  rule [p]: <k> go(X) => done(X) ... </k> requires {rdi() #Equals 97}\n",
        "  syntax IOInt ::= both(Int) [function, symbol(both)]\n  rule both(0) => #getc(0)\n  rule both(_) => #getc(1) [owise]\n  rule [p]: <k> go(X) => done(X) ... </k> requires {both(X) #Equals 97}\n",
        "  syntax Int ::= ff(Int) [function, symbol(ff)]\n  rule [p]: ff(_X) => 1 requires {#getc(0) #Equals 97}\n  rule ff(_) => 0 [owise]\n  rule <k> go(X) => done(ff(X)) ... </k>\n",
    ] {
        let errors = match source_compile_errors(io_source(rule), CompilationBackend::Rust) {
            Ok(()) => panic!("compiles:\n{rule}"),
            Err(errors) => errors,
        };
        let [(code, line, message)] = errors.as_slice() else {
            panic!("{rule}: not one error: {errors:?}");
        };
        assert_eq!(
            (code.as_str(), *line),
            ("MlConstructPosition", Some(io_probed_line(rule))),
            "{rule}: {message}"
        );
        assert!(message.contains("an effect"), "{rule}: {message}");
        assert_eq!(
            source_compile_errors(io_source(rule), CompilationBackend::Llvm),
            Ok(()),
            "{rule}: the LLVM target"
        );
    }
}

/// What the effect refusal leaves alone: a Bool condition (no predicate operand); `#log`, whose
/// value is `.K` whatever it writes and whose output a predicate does not perform; an `impure`
/// function evaluated by its equations; an effect outside every predicate; and a function with an
/// effect-free equation (`sel`), whose application that equation decides has its ordinary value.
/// The rules over `sel` give the answers they gave before the refusal existed.
#[test]
fn an_effect_outside_a_predicate_operand_or_with_a_declared_result_compiles() {
    for rule in [
        "  rule [p]: <k> go(X) => done(X) ... </k> requires isInt(#getc(0))\n",
        "  rule [p]: <k> go(X) => done(X) ... </k> requires {#log(\"x\") #Equals .K}\n",
        "  syntax Int ::= pureish() [function, impure, symbol(pureish)]\n  rule pureish() => 7\n  rule [p]: <k> go(X) => done(X) ... </k> requires {pureish() #Equals 7}\n",
        "  rule [p]: <k> go(X) => done(#getc(0)) ... </k> requires {X #Equals 97}\n",
    ] {
        assert_eq!(
            source_compile_errors(io_source(rule), CompilationBackend::Rust),
            Ok(()),
            "{rule}"
        );
    }
    // The `<k>` items the runs reach. A run reaching `done(V)` goes on to the rule of `io_source`
    // that reads the console, which the library route leaves unevaluated, so only the reached
    // term is compared.
    let done = |n: &str| vec![format!("done({n})")];
    let ground =
        format!("{SEL}  rule [p]: <k> go(X) => done(X) ... </k> requires {{sel(5) #Equals 5}}\n");
    let kore = compile_source(io_source(&ground), CompilationBackend::Rust).definition_kore;
    let leaves = |n: i64| -> Vec<String> {
        run_kore_states(&kore, n)
            .into_iter()
            .map(|(_, k, _)| k)
            .collect()
    };
    assert_eq!(leaves(5), done("5"), "{ground}");
    assert_eq!(leaves(97), done("97"), "{ground}");
    let open =
        format!("{SEL}  rule [p]: <k> go(X) => done(X) ... </k> requires {{sel(X) #Equals 5}}\n");
    let kore = compile_source(io_source(&open), CompilationBackend::Rust).definition_kore;
    let leaves = |n: i64| -> Vec<String> {
        run_kore_states(&kore, n)
            .into_iter()
            .map(|(_, k, _)| k)
            .collect()
    };
    assert_eq!(leaves(5), done("5"), "{open}");
    // sel(97) = 97, so the condition does not hold and go(97) does not step.
    assert_eq!(leaves(97), vec!["go(97)".to_owned()], "{open}");
}

/// On the search route, an effect inside a predicate operand of the condition is refused at
/// compile with the route's code, located at the pattern.
#[test]
fn an_effect_inside_a_search_pattern_predicate_operand_is_refused() {
    for contents in [
        "<k> done(X) </k> requires {#getc(0) #Equals 97}",
        "<k> done(X) </k> requires #Ceil(rd())",
        "<k> done(X) </k> requires {#trace(X) #Equals .K}",
    ] {
        let (code, line, message) = pattern_refusal(io_source(""), contents);
        assert_eq!(
            (code.as_str(), line),
            ("InvalidSearchPattern", Some(1)),
            "{contents}: {message}"
        );
        assert!(message.contains("an effect"), "{contents}: {message}");
    }
    // `sel(5)` is 5 by an effect-free equation.
    let pattern = "<k> done(X) </k> requires {sel(5) #Equals 5}";
    try_compile_pattern_source(io_source(SEL), pattern)
        .unwrap_or_else(|error| panic!("{pattern}: {error}"));
}

/// `krust krun --pattern` prints each found state under every condition the search left on it: a
/// ground equality of a function application that no equation evaluates (`uf(3) = 30`, `pf(3) =
/// 30`) is a condition of the match, as the library result states it, not the name of a
/// generated variable.
#[cfg(feature = "cli")]
#[test]
fn krun_pattern_prints_a_ground_function_equality_of_a_match() {
    let sentences = format!(
        "{BRANCHES}  syntax Int ::= uf(Int) [function, total, symbol(uf)]\n  syntax Int ::= pf(Int) [function, symbol(pf)]\n  rule pf(1) => 10\n  rule pf(2) => 20\n"
    );
    let equality = |function: &str, n: i64| {
        format!(
            "\\equals{{SortInt{{}},SortGeneratedTopCell{{}}}}(Lbl{function}{{}}(\\dv{{SortInt{{}}}}(\"{n}\")),\\dv{{SortInt{{}}}}(\"30\"))"
        )
    };
    for (condition, function, states) in [
        ("uf(X) ==Int 30", "uf", &[1, 2, 3][..]),
        ("{uf(X) #Equals 30}", "uf", &[1, 2, 3][..]),
        ("{pf(X) #Equals 30}", "pf", &[3][..]),
    ] {
        let (status, stdout, stderr) = krun_pattern(
            &sentences,
            &format!("<k> done(X) </k> requires {condition}"),
        );
        assert_eq!(status, 0, "{condition}: {stderr}");
        let printed = stdout.split_whitespace().collect::<String>();
        for n in states {
            assert!(
                printed.contains(&equality(function, *n)),
                "{condition}: no {} in {printed}",
                equality(function, *n)
            );
        }
    }
}

/// Two quantifiers that spell their variables alike bind two variables, each at its own sort:
/// `(#Exists Y:Int . {A #Equals Y}) #And (#Exists Y:KItem . {B #Equals Y})` holds where `A` is an
/// Int and `B` is anything, as the spelling with `Z` does.
#[cfg(any(feature = "z3-inference", feature = "cli"))]
const SAME_SPELLED_BINDERS: [&str; 2] = [
    "(#Exists Y:Int . {A #Equals Y}) #And (#Exists Y:KItem . {B #Equals Y})",
    "(#Exists Y:Int . {A #Equals Y}) #And (#Exists Z:KItem . {B #Equals Z})",
];

#[cfg(feature = "cli")]
const PAIRS: &str = "  syntax KItem ::= pr(KItem, KItem) [symbol(pr)] | \"a\" [symbol(a)]\n  rule [s1]: <k> go(0) => pr(1, a) ... </k>\n  rule [s2]: <k> go(0) => pr(2, 2) ... </k>\n";

/// A rule whose condition holds two same-spelled binders at different sorts fires where the
/// condition holds. The quantified condition needs a solver, which the portable build lacks (it
/// leaves the step indeterminate).
#[cfg(feature = "z3-inference")]
#[test]
fn a_rule_with_same_spelled_binders_at_two_sorts_fires_where_its_condition_holds() {
    for condition in SAME_SPELLED_BINDERS {
        let sentences = format!(
            "  syntax KItem ::= pr(KItem, KItem) [symbol(pr)] | \"a\" [symbol(a)]\n  rule [s1]: <k> go(0) => pr(1, a) ... </k>\n  rule [r]: <k> pr(A, B) => done(7) ... </k> requires {condition}\n"
        );
        assert_eq!(run(&sentences, 0), stuck("done(7)"), "{condition}");
    }
}

/// A search pattern whose condition holds two same-spelled binders at different sorts finds
/// both states where it holds.
#[cfg(feature = "cli")]
#[test]
fn krun_pattern_with_same_spelled_binders_at_two_sorts_finds_both_states() {
    let bound = |n: &str| {
        format!("VarA:SortKItem{{}},inj{{SortInt{{}},SortKItem{{}}}}(\\dv{{SortInt{{}}}}(\"{n}\"))")
    };
    for condition in SAME_SPELLED_BINDERS {
        let (status, stdout, stderr) =
            krun_pattern(PAIRS, &format!("<k> pr(A, B) </k> requires {condition}"));
        assert_eq!(status, 0, "{condition}: {stderr}");
        let printed = stdout.split_whitespace().collect::<String>();
        for n in ["1", "2"] {
            assert!(
                printed.contains(&bound(n)),
                "{condition}: no A = {n} in {printed}"
            );
        }
    }
}
