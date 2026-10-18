//! A condition is emitted as the predicate it states: the matching-logic connectives at its root
//! are predicate connectives at the sentence's sort, the atoms `#Equals`, `#Ceil`, `#Floor` and
//! `#In` keep their operand sort and take the sentence's sort, and each Bool term directly below
//! that spine is the predicate `\equals{SortBool{}, R}(t, \dv{SortBool{}}("true"))`. A plain Bool
//! condition is one such leaf, so its KORE is the leaf alone. The LLVM target keeps the Bool-term
//! form, which is what its interpreter evaluates.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    builtin::embedded,
    definition::{CheckMode, Sentence},
    kast::Term,
    kompile::{
        CompilationBackend, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition,
    },
    kore::{ast::Pattern, codec, parser::parse_pattern, printer::Printer},
    outer::{LoadOptions, ResolvedSource, load_for_compilation, load_with_options},
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
    let source = format!("{HEADER}{sentences}endmodule\n");
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

/// The axiom labelled `label`, whitespace collapsed.
fn axiom(kore: &str, label: &str) -> String {
    let needle = format!("label{{}}(\"{label}\")");
    let at = kore
        .find(&needle)
        .unwrap_or_else(|| panic!("no axiom labelled {label}"));
    let start = kore[..at]
        .rfind("axiom{")
        .expect("an axiom precedes its label");
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
