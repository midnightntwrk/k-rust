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
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition,
        compile_search_pattern,
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
            "axiom{R} \\implies{R}(\\exists{R}(Var'Unds'Gen1:SortInt{}, \\equals{SortBool{}, R}(Lbl'UndsEqlsEqls'Int'Unds'{}(VarX:SortInt{}, Lbl'UndsPlus'Int'Unds'{}(Var'Unds'Gen1:SortInt{}, \\dv{SortInt{}}(\"1\"))), \\dv{SortBool{}}(\"true\"))),"
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
    let kore = compile(sentences);
    let mut backend = Backend::new(&kore, "P", BackendOptions::default()).unwrap();
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
        .map_err(|error| error.to_string())
}

/// `kcompile --for-proving` of module P-SPEC (`claims`) over P (`sentences`).
fn try_compile_spec(sentences: &str, claims: &str) -> Result<String, String> {
    let source =
        format!("{HEADER}{sentences}endmodule\n\nmodule P-SPEC\n  imports P\n{claims}endmodule\n");
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
            ..CompilationBackend::Rust.load_options()
        },
    )
    .expect("the specification loads");
    compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend: CompilationBackend::Rust,
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: "P".to_owned(),
            },
            ..CompileOptions::default()
        },
    )
    .map(|artifacts| artifacts.definition_kore)
    .map_err(|error| error.to_string())
}

/// The refusal names the sentence by kind, label and position, and states both reasons.
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
    let at = format!("{sentence} at ml_conditions.k:{line}:");
    assert!(message.contains(&at), "{condition}: no {at:?} in {message}");
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
    let compiled = compile_search_pattern(&parsing, &execution, "P", contents, attributes)
        .unwrap_or_else(|error| panic!("{contents}: {error}"));
    Printer::compact().print_pattern(&compiled.pattern)
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
    let axiom = axiom(
        &compile("  rule [p]: <k> go(X) => done((X #Or 0) #And 1) ... </k>\n"),
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
    let artifacts = compile_artifacts(
        &format!("{F}  rule [p]: f(X) => X #And 1\n{G}"),
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
    let [equality] = &equalities[..] else {
        panic!(
            "one generated equality in module P, found {}",
            equalities.len()
        )
    };
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
    // The copy is a node the lowering creates: its origin names the pass and links X's span.
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

/// The specification `rules` (in module P), the claims `claims` (in module P-SPEC), and the
/// verdict of proving the claim labelled `claim`.
fn prove(rules: &str, claims: &str, claim: &str) -> String {
    let kore = try_compile_spec(rules, claims).expect("the specification compiles");
    let mut backend = Backend::new(&kore, "P-SPEC", BackendOptions::default()).unwrap();
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
  configuration <k> $PGM:Pgm </k>
  syntax KItem ::= done(IOInt) [symbol(done)] | res(IOInt, IOInt) [symbol(res)] | wdone(K) [symbol(wdone)]
  syntax IOInt ::= rd() [function, symbol(rd)]
  rule rd() => #getc(0)
  rule <k> done(V:Int) => res(V, #getc(0)) ... </k>
{rules}endmodule
"
    )
}

/// An operand that applies an `impure` production, directly or through a function whose
/// equations do, performs an effect when it is evaluated: copying it into an equality would
/// duplicate the effect, and the equality is a predicate, where no effect is performed. Such a
/// conjunction is emitted as written.
#[test]
fn a_conjunction_with_an_effectful_operand_is_not_lowered() {
    for (label, conjunction) in [
        ("first", "#getc(0) #And X"),
        ("second", "X #And #getc(0)"),
        ("through", "rd() #And X"),
        ("chain", "#getc(0) #And X #And 1"),
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
    for conjunction in ["#getc(0) #And X", "X #And #getc(0)"] {
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
