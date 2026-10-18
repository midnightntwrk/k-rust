//! A condition is emitted as the predicate it states: the matching-logic connectives at its root
//! are predicate connectives at the sentence's sort, the atoms `#Equals`, `#Ceil`, `#Floor` and
//! `#In` keep their operand sort and take the sentence's sort, and each Bool term directly below
//! that spine is the predicate `\equals{SortBool{}, R}(t, \dv{SortBool{}}("true"))`. A plain Bool
//! condition is one such leaf, so its KORE is the leaf alone. The LLVM target keeps the Bool-term
//! form, which is what its interpreter evaluates.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    builtin::embedded,
    definition::CheckMode,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{ast::Pattern, codec, parser::parse_pattern},
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
    .definition_kore
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
    // Until guard_or_patterns stops aliasing conditions (MLP/1), the disjunction is conjoined
    // with its alias read as a Bool leaf; the spine is a predicate either way.
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

// ---------------------------------------------------------------- an equality of a predicate and a Bool term

/// The conditions whose spine holds an `#Equals` between a non-term pattern and a Bool term,
/// each with the case its refusal explains: `predicate` (a predicate at sort Bool is all of Bool
/// or nothing, never one Bool value) or `connective` (a connective over Bool terms denotes a set
/// of values, not a condition).
const EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM: &[(&str, &str)] = &[
    ("{ {X #Equals 1} #Equals true }", "predicate"),
    ("{ #Ceil(1 /Int (X -Int 1)) #Equals true }", "predicate"),
    ("#Not({ {X #Equals 1} #Equals true })", "predicate"),
    ("{ {X #Equals 1} #Equals false }", "predicate"),
    (
        "(X >Int 0) #And { (X >Int 5) #Equals #Ceil(1 /Int X) }",
        "predicate",
    ),
    (
        "{ true #Equals ((X ==Int 1) #Or (X ==Int 2)) }",
        "connective",
    ),
    (
        "{ ((X ==Int 1) #And (X ==Int 2)) #Equals false }",
        "connective",
    ),
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

/// The refusal names the sentence by kind, label and position, and explains its case.
#[track_caller]
fn assert_refused(
    result: Result<String, String>,
    sentence: &str,
    line: usize,
    case: &str,
    condition: &str,
) {
    let message = match result {
        Ok(_) => panic!("{condition}: the {sentence} compiles"),
        Err(message) => message,
    };
    let at = format!("{sentence} at ml_conditions.k:{line}:");
    assert!(message.contains(&at), "{condition}: no {at:?} in {message}");
    let reason = match case {
        "predicate" => "a predicate at sort Bool denotes all of Bool or nothing",
        "connective" => "a connective over Bool terms denotes a set of values",
        _ => unreachable!(),
    };
    assert!(
        message.contains(reason),
        "{condition}: no {reason:?} in {message}"
    );
    assert!(
        message.contains("andBool"),
        "{condition}: no remedy in {message}"
    );
}

#[test]
fn a_rule_whose_condition_equates_a_predicate_with_a_bool_term_is_refused() {
    for (condition, case) in EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM {
        let result = try_compile(&format!(
            "  rule [p]: <k> go(X) => done(X) ... </k> requires {condition}\n"
        ));
        assert_refused(result, "rule [P.p]", line_after(""), case, condition);
    }
}

#[test]
fn a_function_equation_whose_condition_equates_a_predicate_with_a_bool_term_is_refused() {
    for (condition, case) in EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM {
        let result = try_compile(&format!(
            "{F}  rule [p]: f(X) => X requires {condition}\n{G}"
        ));
        assert_refused(result, "rule [P.p]", line_after(F), case, condition);
    }
    // In an ensures, at the equation's sort.
    let (condition, case) = EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM[0];
    let result = try_compile(&format!(
        "{F}  rule [p]: f(X) => X ensures {condition}\n{G}"
    ));
    assert_refused(result, "rule [P.p]", line_after(F), case, condition);
}

#[test]
fn a_claim_whose_condition_equates_a_predicate_with_a_bool_term_is_refused() {
    let rule = "  rule [g]: <k> go(X) => done(X) ... </k> requires X =/=Int 1\n";
    // The claim's line: HEADER, the rule, `endmodule`, a blank line, `module P-SPEC`, `imports P`.
    let line = HEADER.lines().count() + 1 + 4 + 1;
    for (condition, case) in EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM {
        let result = try_compile_spec(
            rule,
            &format!("  claim [q]: <k> go(X) => done(X) ... </k> requires {condition}\n"),
        );
        assert_refused(result, "claim [P-SPEC.q]", line, case, condition);
    }
}

/// An owise equation reads its competitors' conditions; the refusal names the competitor.
#[test]
fn an_owise_competitor_whose_condition_equates_a_predicate_with_a_bool_term_is_refused() {
    let (condition, case) = EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM[0];
    let result = try_compile(&format!(
        "{F}  rule [o]: f(_) => 0 [owise]\n  rule [p]: f(X) => 1 requires {condition}\n{G}"
    ));
    assert_refused(result, "rule [P.p]", line_after(F) + 1, case, condition);
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

/// The LLVM target keeps its output, these conditions included. The `#Or` condition is left out:
/// guard_or_patterns aliases a disjunction there, which the test profile's kompile invariants
/// refuse for that target at the base already (MLP/1).
#[test]
fn the_llvm_target_compiles_an_equality_of_a_predicate_and_a_bool_term_as_before() {
    for (condition, _) in EQUALITIES_OF_A_PREDICATE_AND_A_BOOL_TERM
        .iter()
        .filter(|(condition, _)| !condition.contains("#Or"))
    {
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
