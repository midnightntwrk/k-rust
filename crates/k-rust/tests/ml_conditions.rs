//! A condition is emitted as the predicate it states: the matching-logic connectives at its root
//! are predicate connectives at the sentence's sort, the atoms `#Equals`, `#Ceil`, `#Floor` and
//! `#In` keep their operand sort and take the sentence's sort, and each Bool term directly below
//! that spine is the predicate `\equals{SortBool{}, R}(t, \dv{SortBool{}}("true"))`. A plain Bool
//! condition is one such leaf, so its KORE is the leaf alone. The LLVM target keeps the Bool-term
//! form, which is what its interpreter evaluates.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest},
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{ast::Pattern, codec, parser::parse_pattern},
    outer::{LoadOptions, ResolvedSource, load_for_compilation},
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
