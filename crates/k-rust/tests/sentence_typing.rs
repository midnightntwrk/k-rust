//! The public typing view of loaded rule-like sentences (`k_rust::kompile::sentence_typing`).

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Definition, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::{
    CompilationBackend, CompileOptions, PositionTyping, SentenceTyping, SentenceTypingError,
    SortInjectionError, compile_loaded_definition, sentence_typing,
};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation};

const TYPED: &str = include_str!("fixtures/sentence-typing/typed.k");
const PRELUDE: &str = include_str!("fixtures/sentence-typing/portable-prelude.k");

fn load_source(
    name: &str,
    source: &str,
    main: &str,
    implicit: Vec<ResolvedSource>,
) -> LoadedDefinition {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    load_for_compilation(
        ResolvedSource::new(name, source.to_owned()),
        main,
        None,
        &mut resolver,
        &LoadOptions {
            implicit_sources: implicit,
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{error}"))
    .0
}

fn load() -> LoadedDefinition {
    load_source(
        "typed.k",
        TYPED,
        "TYPED",
        vec![
            builtin::embedded("kast.md").unwrap(),
            ResolvedSource::new("portable-prelude.k", PRELUDE.to_owned()),
        ],
    )
}

fn labelled<'a>(definition: &'a Definition, label: &str) -> &'a Sentence {
    definition
        .modules
        .iter()
        .flat_map(|module| module.local_sentences.iter())
        .find(|sentence| sentence.attributes().string(AttributeKey::Label) == Some(label))
        .unwrap_or_else(|| panic!("no sentence {label}"))
}

fn typing(loaded: &LoadedDefinition, label: &str) -> SentenceTyping {
    sentence_typing(
        &loaded.resolved,
        "TYPED",
        labelled(&loaded.definition, label),
    )
    .unwrap_or_else(|error| panic!("{label}: {error}"))
}

fn at<'a>(typing: &'a SentenceTyping, path: &[u32]) -> &'a PositionTyping {
    typing
        .positions
        .get(path)
        .unwrap_or_else(|| panic!("no position {path:?} in {:#?}", typing.positions))
}

fn sorted(sort: Option<&str>, required: Option<&str>) -> PositionTyping {
    PositionTyping {
        sort: sort.map(Sort::new),
        required: required.map(Sort::new),
    }
}

fn term_at<'a>(sentence: &'a mut Sentence, path: &[u32]) -> &'a mut Term {
    let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = sentence
    else {
        panic!("expected a rule")
    };
    let mut term = match path[0] {
        0 => body,
        1 => requires,
        _ => ensures,
    };
    for step in &path[1..] {
        while let Term::Annotated { term: inner, .. } = term {
            term = inner;
        }
        term = match term {
            Term::Rewrite { left, right } => {
                if *step == 0 {
                    left
                } else {
                    right
                }
            }
            Term::Apply { arguments, .. } => &mut arguments[*step as usize],
            other => panic!("no child {step} in {other}"),
        };
    }
    term
}

fn edited(loaded: &LoadedDefinition, label: &str, path: &[u32], replacement: Term) -> Sentence {
    let mut sentence = labelled(&loaded.definition, label).clone();
    *term_at(&mut sentence, path) = replacement;
    sentence
}

// increment: counter(#SemanticCastToNat(N), s(#SemanticCastToNat(L)))
//         => counter(s(#SemanticCastToNat(N)), #SemanticCastToNat(L))
#[test]
fn reports_sorts_and_required_sorts_of_a_loaded_rule() {
    let loaded = load();
    let typing = typing(&loaded, "TYPED.increment");

    assert_eq!(at(&typing, &[0]), &sorted(Some("Counter"), None));
    assert_eq!(
        at(&typing, &[0, 1]),
        &sorted(Some("Counter"), Some("Counter"))
    );
    assert_eq!(at(&typing, &[0, 1, 0]), &sorted(Some("Nat"), Some("Nat")));
    assert_eq!(
        at(&typing, &[0, 1, 0, 0]),
        &sorted(Some("Nat"), Some("Nat"))
    );
    assert_eq!(
        at(&typing, &[0, 1, 0, 0, 0]),
        &sorted(Some("Nat"), Some("Nat"))
    );
    assert_eq!(at(&typing, &[1]), &sorted(Some("Bool"), Some("Bool")));
    assert_eq!(at(&typing, &[2]), &sorted(Some("Bool"), Some("Bool")));
    assert_eq!(typing.variables.get("N"), Some(&Sort::new("Nat")));
    assert_eq!(typing.variables.get("L"), Some(&Sort::new("Nat")));
}

// A rewrite's sides are placed at their least upper bound, as the injector places them.
#[test]
fn rewrite_sides_require_their_least_upper_bound() {
    let loaded = load();
    let sentence = edited(
        &loaded,
        "TYPED.increment",
        &[0, 1],
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
    );
    let typing = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap();

    assert_eq!(at(&typing, &[0]), &sorted(Some("KItem"), None));
    assert_eq!(
        at(&typing, &[0, 0]),
        &sorted(Some("Counter"), Some("KItem"))
    );
    assert_eq!(at(&typing, &[0, 1]), &sorted(Some("Bool"), Some("KItem")));
}

// The overloaded `neg` resolves to the production the parser chose at each position: the Small
// overload requires a Small argument.
#[test]
fn overloaded_applications_report_the_selected_production() {
    let loaded = load();
    let typing = typing(&loaded, "TYPED.overload");

    assert_eq!(at(&typing, &[0, 0]).sort, Some(Sort::new("Small")));
    assert_eq!(at(&typing, &[0, 0, 0]).required, Some(Sort::new("Small")));
    assert_eq!(at(&typing, &[0, 1, 0]).required, Some(Sort::new("Small")));
}

// Authored cells keep their `#noDots`/`#dots` markers and the `#cells` wrapper at the loaded
// layer; these report no sort, and a leaf cell's body is placed at the cell's content sort.
#[test]
fn cell_fragments_report_no_sort_and_leaf_bodies_their_content_sort() {
    let loaded = load();
    let typing = typing(&loaded, "TYPED.cell");

    assert_eq!(at(&typing, &[0]), &sorted(None, None));
    assert_eq!(at(&typing, &[0, 0]).sort, Some(Sort::new("KCell")));
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(None, None));
    assert_eq!(at(&typing, &[0, 0, 1]).required, Some(Sort::new("K")));
    assert_eq!(at(&typing, &[0, 0, 2]), &sorted(None, None));
    assert_eq!(at(&typing, &[0, 1, 1]).required, Some(Sort::new("Nat")));
    assert_eq!(
        at(&typing, &[0, 1, 1, 0]),
        &sorted(Some("Nat"), Some("Nat"))
    );
}

// Each anonymous variable takes the sort of its own cast.
#[test]
fn anonymous_variables_take_their_own_cast_sort() {
    let loaded = load();
    let typing = typing(&loaded, "TYPED.anonymous");

    assert_eq!(at(&typing, &[0, 0, 0, 0]).sort, Some(Sort::new("Int")));
    assert_eq!(at(&typing, &[0, 0, 1, 0]).sort, Some(Sort::new("Nat")));
}

// A sortless variable that no cast types reports no sort; the view does not infer one.
#[test]
fn an_undetermined_variable_reports_no_sort() {
    let loaded = load();
    let sentence = edited(
        &loaded,
        "TYPED.increment",
        &[0, 0, 0],
        Term::Variable {
            name: "Q".into(),
            sort: None,
        },
    );
    let typing = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap();

    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(None, Some("Nat")));
    assert!(!typing.variables.contains_key("Q"));
}

#[test]
fn a_sentence_the_compiler_rejects_returns_the_same_error() {
    let loaded = load();
    let ill_sorted = edited(
        &loaded,
        "TYPED.increment",
        &[0, 1, 0],
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
    );
    let error = sentence_typing(&loaded.resolved, "TYPED", &ill_sorted).unwrap_err();
    assert!(
        matches!(&error, SentenceTypingError::Sort { error: SortInjectionError::IllSortedTerm(mismatch), .. }
            if mismatch.found == Sort::new("Bool") && mismatch.required == Sort::new("Nat")),
        "{error}"
    );
    assert!(error.to_string().starts_with("typed.k:"), "{error}");

    let incomparable = edited(
        &loaded,
        "TYPED.increment",
        &[0, 1, 0],
        Term::apply(
            "#SemanticCastToNat",
            vec![Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            }],
        ),
    );
    let error = sentence_typing(&loaded.resolved, "TYPED", &incomparable).unwrap_err();
    assert!(
        matches!(
            &error,
            SentenceTypingError::Sort {
                error: SortInjectionError::IncomparableCast(_),
                ..
            }
        ),
        "{error}"
    );

    let conflicting = edited(
        &loaded,
        "TYPED.branch",
        &[0],
        Term::Rewrite {
            left: Box::new(Term::apply(
                "#SemanticCastToBool",
                vec![Term::Variable {
                    name: "B".into(),
                    sort: None,
                }],
            )),
            right: Box::new(Term::apply(
                "#SemanticCastToNat",
                vec![Term::Variable {
                    name: "B".into(),
                    sort: None,
                }],
            )),
        },
    );
    let error = sentence_typing(&loaded.resolved, "TYPED", &conflicting).unwrap_err();
    assert!(
        matches!(error, SentenceTypingError::SemanticCasts(_)),
        "{error}"
    );
}

/// Every rule and claim of `loaded` has a typing, every position whose term and requirement have
/// sorts is well placed, and the definition compiles; replacing a subterm by itself therefore
/// keeps a sentence the compiler accepts.
fn assert_view_agrees_with_compilation(loaded: &LoadedDefinition) -> usize {
    let mut checked = 0;
    for module in &loaded.definition.modules {
        for sentence in &module.local_sentences {
            if !matches!(&**sentence, Sentence::Rule { .. } | Sentence::Claim { .. }) {
                continue;
            }
            let typing = sentence_typing(&loaded.resolved, &module.name, sentence)
                .unwrap_or_else(|error| panic!("{}: {error}\n{sentence:?}", module.name));
            checked += typing.positions.len();
        }
    }
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        compile_loaded_definition(
            loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend}: {error} {:?}", error.diagnostics));
    }
    checked
}

#[test]
fn every_loaded_rule_of_the_portable_fixtures_is_typed_and_compiles() {
    assert!(assert_view_agrees_with_compilation(&load()) > 0);
}

#[cfg(feature = "z3-inference")]
#[test]
fn every_loaded_rule_of_the_prelude_and_a_cell_definition_is_typed_and_compiles() {
    let source = r#"
requires "domains.md"
module SHAPES-SYNTAX
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  syntax Exp ::= Int | Exp "+" Exp [strict, symbol(plus)]
  syntax KResult ::= Int
endmodule

module SHAPES
  imports SHAPES-SYNTAX
  imports INT
  imports BOOL
  imports MAP
  imports LIST
  configuration <k> $PGM:Exp </k> <env> .Map </env> <n> 0 </n> <log> .List </log>

  syntax Int ::= f(Int) [function, symbol(f)]
  rule f(X) => X +Int 1 requires X >Int 0
  rule f(_) => 0 [owise]
  rule [add]: <k> I1:Int + I2:Int => I1 +Int I2 ... </k> <env> M => M[I1 <- I2] </env> <log> ... .List => ListItem(I1) </log>
  rule [anon]: <k> _:Int + _ => 0 ... </k> <n> N => N +Int 1 </n>
  syntax KItem ::= "go"
  rule [fresh]: <k> go => !I:Int ... </k>
  rule [lookup]: <k> I:Int => {M[I]}:>Int ... </k> <env> M </env> requires I in_keys(M)
endmodule
"#;
    let loaded = load_source(
        "shapes.k",
        source,
        "SHAPES",
        vec![builtin::embedded("prelude.md").unwrap()],
    );
    assert!(assert_view_agrees_with_compilation(&loaded) > 0);
}
