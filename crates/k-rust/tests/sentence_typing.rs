//! The public typing view of loaded rule-like sentences (`k_rust::kompile::sentence_typing`).

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Definition, ResolvedDefinition, Sentence};
use k_rust::inner::{ParseError, RuleError};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::{
    BranchTyping, CompilationBackend, CompileOptions, PositionTyping, SentenceTyper,
    SentenceTyping, SentenceTypingError, SortInjectionError, SortInjector,
    compile_loaded_definition, sentence_typing,
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
        loaded.resolved(),
        "TYPED",
        labelled(loaded.definition(), label),
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
    let mut sentence = labelled(loaded.definition(), label).clone();
    *term_at(&mut sentence, path) = replacement;
    sentence
}

// increment: counter(#SemanticCastToNat(N), s(#SemanticCastToNat(L)))
//         => counter(s(#SemanticCastToNat(N)), #SemanticCastToNat(L))
#[test]
fn reports_sorts_and_required_sorts_of_a_loaded_rule() {
    let loaded = load();
    let typing = typing(&loaded, "TYPED.increment");

    // Both branches of the top-level rewrite are Counter, placed at their bound Counter.
    assert_eq!(at(&typing, &[0]), &sorted(Some("Counter"), Some("Counter")));
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

// A rewrite's sides are placed at their least upper bound, as the injector places them; the
// rewrite's own position holds a different side in each branch.
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
    let typing = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap();

    assert_eq!(
        typing.branches.get(&[0]),
        Some(&BranchTyping {
            left: sorted(Some("Counter"), Some("KItem")),
            right: sorted(Some("Bool"), Some("KItem")),
        })
    );
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
    let typing = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap();

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
    let error = sentence_typing(loaded.resolved(), "TYPED", &ill_sorted).unwrap_err();
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
    let error = sentence_typing(loaded.resolved(), "TYPED", &incomparable).unwrap_err();
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

    // `KConfigVar < KItem` (BASIC-K), so `.K` cast to `KConfigVar` lies below its operand's sort.
    let unprojectable = edited(
        &loaded,
        "TYPED.increment",
        &[0, 1, 0],
        Term::apply(
            "#SemanticCastToKConfigVar",
            vec![Term::Sequence(Vec::new())],
        ),
    );
    let error = sentence_typing(loaded.resolved(), "TYPED", &unprojectable).unwrap_err();
    assert!(
        matches!(
            &error,
            SentenceTypingError::Sort {
                error: SortInjectionError::CastBelowOperand(mismatch),
                ..
            } if mismatch.found == Sort::new("K") && mismatch.required == Sort::new("KConfigVar")
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
    let error = sentence_typing(loaded.resolved(), "TYPED", &conflicting).unwrap_err();
    assert!(
        matches!(error, SentenceTypingError::SemanticCasts(_)),
        "{error}"
    );
}

fn var(name: &str, sort: Option<&str>) -> Term {
    Term::Variable {
        name: name.into(),
        sort: sort.map(Sort::new),
    }
}

fn cast(sort: &str, term: Term) -> Term {
    Term::apply(format!("#SemanticCastTo{sort}"), vec![term])
}

fn as_pattern(pattern: Term, alias: Term) -> Term {
    Term::As {
        pattern: Box::new(pattern),
        alias: Box::new(alias),
    }
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn relinked(
    loaded: &LoadedDefinition,
    module: &str,
    label: &str,
    sentence: Sentence,
) -> LoadedDefinition {
    let mut definition = loaded.definition().clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|candidate| candidate.name == module)
        .unwrap();
    let slot = module
        .local_sentences
        .iter_mut()
        .find(|candidate| candidate.attributes().string(AttributeKey::Label) == Some(label))
        .unwrap();
    *k_rust::definition::sentence_mut(slot) = sentence;
    loaded.with_definition(definition).unwrap()
}

fn compiled_kore(loaded: &LoadedDefinition) -> Result<String, k_rust::kompile::CompileError> {
    compile_loaded_definition(loaded, CompileOptions::default())
        .map(|artifacts| artifacts.definition_kore)
}

/// `source` parsed and lowered with `MAIN` as its main module, its bubbles left unparsed.
fn unparsed(source: &str) -> Definition {
    let parsed = k_rust::outer::parse("lowered.k", source).expect("definition should parse");
    k_rust::outer::lower(&parsed, "MAIN").expect("definition should lower")
}

fn lowered(source: &str) -> (Definition, ResolvedDefinition) {
    let definition = k_rust::inner::resolve_rule_bubbles(&unparsed(source))
        .expect("rule bubbles should resolve");
    let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
    (definition, resolved)
}

// Only parser sorts can lie above `K` (`KList ::= K`, from the prelude): a user sort is below
// `KItem`, so a user sort above `K` makes the order circular. An `Int` is a `K` only as the one-element sequence
// of a `KItem`, and the emitted theory has no subsort axiom into `K`, so no single injection
// takes an `Int` to `KList`: the injector places `1` at `KList` as
// `inj{K, KList}(inj{Int, KItem}(1) ~> .K)`, and the view accepts it at `KList`.
#[test]
fn a_term_below_k_at_a_position_above_k_is_injected_as_a_sequence() {
    let (_, resolved) = lowered(indoc::indoc! {r#"
        module MAIN
          syntax K
          syntax KItem
          syntax K ::= KItem
          syntax KList ::= K
          syntax Int ::= r"[0-9]+" [token]
          syntax KItem ::= Int
          syntax Holder ::= hold(KList) [symbol(hold)]
        endmodule
    "#});
    // The rule grammar places every sort below `KItem`, so no parsed rule has a position above
    // `K`; the rule is structured.
    let int = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    };
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let rule = Sentence::Rule {
        body: rewrite(
            Term::apply("hold", vec![int("1")]),
            Term::apply("hold", vec![int("2")]),
        ),
        requires: truth.clone(),
        ensures: truth,
        attributes: Default::default(),
    };
    let typing = sentence_typing(&resolved, "MAIN", &rule).unwrap();
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(Some("Int"), Some("KList")));

    let injected = SortInjector::new(&resolved, "MAIN")
        .unwrap()
        .inject_sentence(
            &k_rust::kompile::resolve_semantic_casts_in_sentence(
                &resolved
                    .subsorts(resolved.module_id("MAIN").unwrap())
                    .unwrap(),
                rule,
            )
            .unwrap(),
        )
        .unwrap();
    let Sentence::Rule { body, .. } = injected else {
        unreachable!()
    };
    let body = body.to_string();
    assert!(body.contains("inj{K,KList}"), "{body}");
    assert!(body.contains("inj{Int,KItem}"), "{body}");
    assert!(!body.contains("inj{Int,KList}"), "{body}");
    assert!(!body.contains("inj{KItem,KList}"), "{body}");
}

// A user sort is a sort of K items, below `KItem`, so `syntax Above ::= K` closes the cycle
// `KItem < K < Above < KItem`: the declaration contradicts the position of `K` above every K item.
// No rule grammar can be built for such a view, so rule-bubble resolution rejects it with the
// cycle before building one. The definition has no bubble, so its resolved definition is read
// directly, and the typer reports the circular order too.
#[test]
fn a_user_sort_above_k_is_circular() {
    let definition = unparsed(indoc::indoc! {r#"
        module MAIN
          syntax K
          syntax KItem
          syntax K ::= KItem
          syntax Above ::= K
        endmodule
    "#});
    assert!(
        matches!(
            k_rust::inner::resolve_rule_bubbles(&definition),
            Err(RuleError::Parse(error))
                if matches!(&error.error, ParseError::CircularSubsorts { path }
                    if path.contains(&Sort::new("Above")))
        ),
        "a user sort above K is rejected before a rule grammar is built"
    );
    let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
    assert!(matches!(
        SentenceTyper::new(&resolved, "MAIN"),
        Err(SentenceTypingError::Sort {
            error: SortInjectionError::CircularSubsort(_),
            ..
        })
    ));
}

// A cast on an as-pattern fixes the sort both sides are placed at, before any least upper bound:
// `P #as A` is one value, so `#SemanticCastToBool(z #as B:Bool)` constrains each side as a cast
// written on it would, and `z:Bool` casts a `Nat` to an incomparable sort, which compilation
// rejects as it rejects that cast written directly.
#[test]
fn a_cast_as_pattern_places_both_sides_at_the_cast_sort() {
    let loaded = load();
    let ill_sorted = edited(
        &loaded,
        "TYPED.branch",
        &[0, 0, 0],
        cast(
            "Bool",
            as_pattern(Term::apply("z", vec![]), var("_B2", Some("Bool"))),
        ),
    );
    let error = sentence_typing(loaded.resolved(), "TYPED", &ill_sorted).unwrap_err();
    assert!(
        matches!(&error, SentenceTypingError::Sort { error: SortInjectionError::IncomparableCast(mismatch), .. }
            if mismatch.found == Sort::new("Nat") && mismatch.required == Sort::new("Bool")),
        "{error}"
    );
    let compiled = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.branch", ill_sorted));
    assert!(compiled.is_err());

    // `#SemanticCastToKItem(counter(..) #as _C:Counter)` as the left side: both sides at KItem.
    let mut sentence = labelled(loaded.definition(), "TYPED.increment").clone();
    let left = term_at(&mut sentence, &[0, 0]).clone();
    *term_at(&mut sentence, &[0, 0]) = cast("KItem", as_pattern(left, var("_C", Some("Counter"))));
    let typing = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap();
    assert_eq!(
        at(&typing, &[0, 0, 0]),
        &sorted(Some("KItem"), Some("KItem"))
    );
    assert_eq!(
        at(&typing, &[0, 0, 0, 0]),
        &sorted(Some("Counter"), Some("KItem"))
    );
    assert_eq!(
        at(&typing, &[0, 0, 0, 1]),
        &sorted(Some("Counter"), Some("KItem"))
    );
    let kore = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.increment", sentence)).unwrap();
    let i = kore
        .find("COUNTER.increment")
        .or(kore.find("TYPED.increment"))
        .unwrap_or(0);
    assert!(
        kore.contains("inj{SortCounter{}, SortKItem{}}(Var'Unds'C:SortCounter{})"),
        "{}",
        &kore[i.saturating_sub(1500)..(i + 100).min(kore.len())]
    );
}

// A nested rewrite is typed per branch, as compilation projects it:
// `id(z => counter(z, z))` instantiates `id` at `Nat` in the left branch
// and at `Counter` in the right one.
#[test]
fn a_nested_rewrite_is_typed_in_each_branch() {
    let loaded = load();
    let mut sentence = labelled(loaded.definition(), "TYPED.increment").clone();
    *term_at(&mut sentence, &[0]) = Term::apply(
        "id",
        vec![rewrite(
            Term::apply("z", vec![]),
            Term::apply(
                "counter",
                vec![Term::apply("z", vec![]), Term::apply("z", vec![])],
            ),
        )],
    );
    let typing = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap();

    assert_eq!(
        typing.branches.get(&[0]),
        Some(&BranchTyping {
            left: sorted(Some("Nat"), Some("KItem")),
            right: sorted(Some("Counter"), Some("KItem")),
        })
    );
    assert_eq!(
        typing.branches.get(&[0, 0]),
        Some(&BranchTyping {
            left: sorted(Some("Nat"), Some("Nat")),
            right: sorted(Some("Counter"), Some("Counter")),
        })
    );
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(Some("Nat"), Some("Nat")));
    assert_eq!(
        at(&typing, &[0, 0, 1]),
        &sorted(Some("Counter"), Some("Counter"))
    );
    let kore = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.increment", sentence)).unwrap();
    assert!(kore.contains("Lblid{SortNat{}}"), "{kore}");
    assert!(kore.contains("Lblid{SortCounter{}}"), "{kore}");
}

// Typing computes the instance without placing it; compilation rejects the value-building
// `id{Bool}(true)` because Bool's values are fixed by its hook and domain values.
#[test]
fn typing_reports_a_fixed_sort_schema_instance_that_compilation_rejects() {
    let loaded = load();
    let sentence = edited(
        &loaded,
        "TYPED.increment",
        &[0],
        Term::apply(
            "id",
            vec![rewrite(
                Term::apply("z", vec![]),
                Term::Token {
                    token: "true".into(),
                    sort: Sort::new("Bool"),
                },
            )],
        ),
    );
    let typing = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap();
    assert_eq!(
        typing.branches.get(&[0]),
        Some(&BranchTyping {
            left: sorted(Some("Nat"), Some("KItem")),
            right: sorted(Some("Bool"), Some("KItem")),
        })
    );
    assert_eq!(
        typing.branches.get(&[0, 0]),
        Some(&BranchTyping {
            left: sorted(Some("Nat"), Some("Nat")),
            right: sorted(Some("Bool"), Some("Bool")),
        })
    );
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(Some("Nat"), Some("Nat")));
    assert_eq!(at(&typing, &[0, 0, 1]), &sorted(Some("Bool"), Some("Bool")));
    let error = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.increment", sentence))
        .expect_err("the right branch must not build a Bool value with its own id root");
    assert_eq!(error.stage, "add sort injections", "{error}");
    assert!(error.message.contains("the instance of `id`"), "{error}");
    assert!(error.message.contains("is at sort Bool"), "{error}");
}

// The projection copies a rewrite's left side as it is, so a rewrite nested in it stays a rewrite
// in the left branch: `s((z => true) => z)` puts `z => true`, whose sides have no sort below
// `Nat`, at the `Nat` argument of `s`. Compilation rejects it, and so does the view.
#[test]
fn a_rewrite_nested_in_a_left_side_is_typed_as_a_rewrite() {
    let loaded = load();
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let z = || Term::apply("z", vec![]);
    let sentence = edited(
        &loaded,
        "TYPED.increment",
        &[0],
        Term::apply("s", vec![rewrite(rewrite(z(), truth), z())]),
    );
    let error = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap_err();
    assert!(matches!(error, SentenceTypingError::Sort { .. }), "{error}");
    let compiled = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.increment", sentence));
    assert!(compiled.is_err());
}

// The sides of a nested rewrite occupy their parent's argument position, so they take its
// requirement even when neither side has a sort of its own.
#[test]
fn sortless_rewrite_sides_take_the_position_requirement() {
    let loaded = load();
    let sentence = edited(
        &loaded,
        "TYPED.increment",
        &[0],
        Term::apply(
            "counter",
            vec![
                rewrite(var("Q", None), var("R", None)),
                Term::apply("z", vec![]),
            ],
        ),
    );
    let typing = sentence_typing(loaded.resolved(), "TYPED", &sentence).unwrap();

    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(None, Some("Nat")));
    assert_eq!(at(&typing, &[0, 0, 1]), &sorted(None, Some("Nat")));
}

// The free function and a typer built once for the module type every sentence alike, including
// one whose rewrite needs the implicit `KItem` subsorts.
#[test]
fn both_entry_points_agree() {
    let loaded = load();
    let typer = SentenceTyper::new(loaded.resolved(), "TYPED").unwrap();
    let sibling = edited(
        &loaded,
        "TYPED.increment",
        &[0, 1],
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
    );
    for sentence in loaded
        .definition()
        .modules
        .iter()
        .find(|module| module.name == "TYPED")
        .unwrap()
        .local_sentences
        .iter()
        .map(|sentence| (**sentence).clone())
        .filter(|sentence| matches!(sentence, Sentence::Rule { .. }))
        .chain([sibling])
    {
        assert_eq!(
            typer.typing(&sentence),
            sentence_typing(loaded.resolved(), "TYPED", &sentence)
        );
    }
}

/// The KORE spelling of a nullary sort, or `None` for one this check does not spell.
fn kore_sort(sort: &Sort) -> Option<String> {
    (sort.parameters.is_empty() && sort.name.chars().all(|c| c.is_ascii_alphanumeric()))
        .then(|| format!("Sort{}{{}}", sort.name))
}

/// For every position of every rule of `module` where the view places a term of one sort at a
/// position of another, the rule's own axiom in the compiled definition contains the injection
/// that placement emits (a loaded path does not survive cell concretization and the later
/// passes, so the check is per axiom, not per path):
/// `inj{sort, required}`, or at a `K` position `inj{sort, KItem}`, or above `K`
/// `inj{K, required}` over `inj{sort, KItem}`. A cast operand's requirement is the cast's bound,
/// not a placement, and is skipped.
fn assert_view_injections_are_emitted(loaded: &LoadedDefinition, module: &str) -> usize {
    let kore = compiled_kore(loaded).unwrap_or_else(|error| panic!("{error}"));
    let typer = SentenceTyper::new(loaded.resolved(), module).unwrap();
    let mut checked = 0;
    let sentences = loaded
        .definition()
        .modules
        .iter()
        .find(|candidate| candidate.name == module)
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| matches!(&***sentence, Sentence::Rule { .. }));
    for sentence in sentences {
        let typing = typer.typing(sentence).unwrap();
        // Generated rules (configuration initializers) carry no label to find their axiom by.
        let Some(label) = sentence.attributes().string(AttributeKey::Label) else {
            continue;
        };
        let kore = axiom_of(&kore, label);
        let placements = typing
            .positions
            .iter()
            .chain(typing.branches.iter().flat_map(|(path, branches)| {
                [(path.clone(), &branches.left), (path, &branches.right)]
            }));
        for (path, position) in placements {
            let (Some(sort), Some(required)) = (&position.sort, &position.required) else {
                continue;
            };
            if sort == required || under_cast(sentence, &path) {
                continue;
            }
            let (Some(from), Some(to)) = (kore_sort(sort), kore_sort(required)) else {
                continue;
            };
            let direct = format!("inj{{{from}, {to}}}");
            let item = format!("inj{{{from}, SortKItem{{}}}}");
            let through_k = format!("inj{{SortK{{}}, {to}}}");
            let emitted = kore.contains(&direct)
                || (required.name == "K" && (sort.name == "KItem" || kore.contains(&item)))
                || (kore.contains(&through_k) && kore.contains(&item));
            assert!(
                emitted,
                "{module}: {path:?} places {sort} at {required}, but no such injection is emitted"
            );
            checked += 1;
        }
    }
    checked
}

/// The text of the axiom that carries `label`, from its `axiom{` up to the label attribute.
fn axiom_of<'a>(kore: &'a str, label: &str) -> &'a str {
    let attribute = format!("label{{}}(\"{label}\")");
    let end = kore
        .find(&attribute)
        .unwrap_or_else(|| panic!("no axiom labelled {label}"));
    let start = kore[..end]
        .rfind("axiom{")
        .expect("an axiom precedes its attributes");
    &kore[start..end]
}

fn under_cast(sentence: &Sentence, path: &[u32]) -> bool {
    let Some((_, parent)) = path.split_last() else {
        return false;
    };
    if parent.is_empty() {
        return false;
    }
    let mut sentence = sentence.clone();
    matches!(
        term_at(&mut sentence, parent).unannotated(),
        Term::Apply { label, .. } if label.semantic_cast_sort().is_some()
    )
}

#[test]
fn the_views_placements_are_the_emitted_injections() {
    assert!(assert_view_injections_are_emitted(&load(), "TYPED") > 0);
}

/// Every rule and claim of `loaded` has a typing, every position whose term and requirement have
/// sorts is well placed, and the definition compiles; replacing a subterm by itself therefore
/// keeps a sentence the compiler accepts.
fn assert_view_agrees_with_compilation(loaded: &LoadedDefinition) -> usize {
    let mut checked = 0;
    for module in &loaded.definition().modules {
        for sentence in &module.local_sentences {
            if !matches!(&**sentence, Sentence::Rule { .. } | Sentence::Claim { .. }) {
                continue;
            }
            let typing = sentence_typing(loaded.resolved(), &module.name, sentence)
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

// A cast on a rewrite, `plus((E => z):Nat, z)`, types the rewrite and constrains each side (the
// parser also casts the left side), so `E` is a `Nat`. Projecting the rewrite to either side
// leaves no position of its own to the outer cast, so each side, a `Nat`, is placed at the `Exp`
// argument of `plus` itself (as `inj{Nat, Exp}`), while `E` is required at the bound of its own
// cast. The view reports the placements compilation emits.
#[test]
fn a_cast_rewrite_places_its_sides_where_the_rewrite_stands() {
    let source = format!(
        "{TYPED}\nmodule CAST\n  imports TYPED\n  rule [cast]: plus((E => z):Nat, z)\nendmodule\n"
    );
    let loaded = load_source(
        "cast.k",
        &source,
        "CAST",
        vec![
            builtin::embedded("kast.md").unwrap(),
            ResolvedSource::new("portable-prelude.k", PRELUDE.to_owned()),
        ],
    );
    let typing = sentence_typing(
        loaded.resolved(),
        "CAST",
        labelled(loaded.definition(), "CAST.cast"),
    )
    .unwrap();
    assert!(typing.branches.is_empty(), "{:#?}", typing.branches);
    assert_eq!(typing.variables.get("E"), Some(&Sort::new("Nat")));
    // The cast, the rewrite, the left side (`E` under its own cast) and the right side `z`.
    for path in [[0, 0].as_slice(), &[0, 0, 0], &[0, 0, 0, 0], &[0, 0, 0, 1]] {
        assert_eq!(
            at(&typing, path),
            &sorted(Some("Nat"), Some("Exp")),
            "{path:?}"
        );
    }
    assert_eq!(
        at(&typing, &[0, 0, 0, 0, 0]),
        &sorted(Some("Nat"), Some("Nat"))
    );
    assert!(assert_view_injections_are_emitted(&loaded, "CAST") > 0);
    let kore = compiled_kore(&loaded).unwrap();
    assert!(
        axiom_of(&kore, "CAST.cast").contains("inj{SortNat{}, SortExp{}}(VarE:SortNat{})"),
        "{}",
        axiom_of(&kore, "CAST.cast")
    );
}

// ---------------------------------------------------------------------------------------------
// The typing view of the main module: compilation's catalog and view.

/// `source` loaded as kink loads a definition, with the embedded `kast.md` and `prelude.md`
/// implicit, and `requires` resolved from the embedded sources, then from `directory`.
fn load_main(
    name: &str,
    source: &str,
    main: &str,
    directory: Option<&std::path::Path>,
) -> LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required)
            .or_else(|| {
                let path = directory?.join(required);
                let text = std::fs::read_to_string(&path).ok()?;
                Some(ResolvedSource::new(
                    path.to_string_lossy().into_owned(),
                    text,
                ))
            })
            .ok_or_else(|| required.to_owned())
    };
    load_for_compilation(
        ResolvedSource::new(name, source.to_owned()),
        main,
        None,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![
                builtin::embedded("kast.md").unwrap(),
                builtin::embedded("prelude.md").unwrap(),
            ],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{name}: {error}"))
    .0
}

/// The typer of the definition's main module, which types every sentence of its closure.
fn main_typer(loaded: &LoadedDefinition) -> SentenceTyper<'_> {
    let resolved = loaded.resolved();
    SentenceTyper::new(resolved, &resolved.main_module().name).unwrap()
}

/// Every rule and claim of the main module's import closure, with its module's name.
fn closure_sentences(loaded: &LoadedDefinition) -> Vec<(&str, &Sentence)> {
    let resolved = loaded.resolved();
    let main = resolved.main_module_id();
    let closure = resolved.transitive_imports(main);
    loaded
        .definition()
        .modules
        .iter()
        .filter(|module| {
            let id = resolved.module_id(&module.name).unwrap();
            id == main || closure.contains(&id)
        })
        .flat_map(|module| {
            module
                .local_sentences
                .iter()
                .filter(|sentence| {
                    matches!(&***sentence, Sentence::Rule { .. } | Sentence::Claim { .. })
                })
                .map(|sentence| (module.name.as_str(), &**sentence))
        })
        .collect()
}

/// The compiled definition, or the panic that names the failing stage.
fn assert_compiles(loaded: &LoadedDefinition, name: &str) {
    compile_loaded_definition(loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("{name}: {error} {:?}", error.diagnostics));
}

/// Every rule and claim of the main closure types with the main module's typer; the failures
/// are listed together.
fn assert_closure_types(loaded: &LoadedDefinition, name: &str) -> usize {
    let typer = main_typer(loaded);
    let sentences = closure_sentences(loaded);
    let failures = sentences
        .iter()
        .filter_map(|(module, sentence)| {
            typer
                .typing(sentence)
                .err()
                .map(|error| format!("{module}: {error}"))
        })
        .collect::<Vec<_>>();
    assert!(failures.is_empty(), "{name}: {failures:#?}");
    sentences.len()
}

const GENERATED_RULE_SYNTAX: &str =
    include_str!("fixtures/sentence-typing/generated-rule-syntax.k");
const PRIVATE_HELPERS: &str = include_str!("fixtures/sentence-typing/private-helpers.k");
const INFERRED_PARENT: &str = include_str!("fixtures/sentence-typing/inferred-parent.k");
const OWN_PREDICATE: &str = include_str!("fixtures/sentence-typing/own-predicate.k");

// Sort predicates, sort and field projections, local functions and `:=K`/`:/=K` have no
// production in the loaded module; compilation declares or lowers them, and the main module's
// typer types them in compilation's catalog.
#[test]
fn a_rule_using_generated_rule_syntax_types() {
    let loaded = load_main(
        "generated-rule-syntax.k",
        GENERATED_RULE_SYNTAX,
        "TYPER-PROBE",
        None,
    );
    assert_compiles(&loaded, "TYPER-PROBE");
    assert_closure_types(&loaded, "TYPER-PROBE");
    let typer = main_typer(&loaded);
    let typed = |label: &str| {
        typer
            .typing(labelled(loaded.definition(), label))
            .unwrap_or_else(|error| panic!("{label}: {error}"))
    };

    // `Bool ::= isInt(K)`: the predicate is a Bool condition and its argument stands at `K`.
    let predicate = typed("TYPER-PROBE.pred-int");
    assert_eq!(at(&predicate, &[1]), &sorted(Some("Bool"), Some("Bool")));
    assert_eq!(at(&predicate, &[1, 0]).required, Some(Sort::new("K")));

    // `Int ::= fst(Pair)`: the field projection is an `Int` argument of `b`, and its argument a
    // `Pair`.
    let field = typed("TYPER-PROBE.field");
    assert_eq!(at(&field, &[0, 1, 0]), &sorted(Some("Int"), Some("Int")));
    assert_eq!(
        at(&field, &[0, 1, 0, 0]),
        &sorted(Some("Pair"), Some("Pair"))
    );

    // `{X}:>Int` is `Int ::= project:Int(K)`.
    let projection = typed("TYPER-PROBE.proj");
    assert_eq!(at(&projection, &[0, 1, 0]).sort, Some(Sort::new("Int")));
}

// PRIV-B reaches `Foo` and `pair` only through a private import, so PRIV's rule grammar offers
// neither `isFoo` nor `fst`; compilation still declares both over the closure it injects, and
// PRIV-B's rules use them.
#[test]
fn a_helper_of_a_privately_imported_sort_types_in_the_main_view() {
    let loaded = load_main("private-helpers.k", PRIVATE_HELPERS, "PRIV", None);
    assert_compiles(&loaded, "PRIV");
    assert_closure_types(&loaded, "PRIV");
    let typer = main_typer(&loaded);
    let field = typer
        .typing(labelled(loaded.definition(), "PRIV-B.field"))
        .unwrap();
    assert_eq!(at(&field, &[0, 1, 0]), &sorted(Some("Int"), Some("Int")));
    assert_eq!(at(&field, &[0, 1, 0, 0]).sort, Some(Sort::new("Pair")));
}

// A projection whose parent's instance the injector infers (`#if`, `#Equals`) is typed by the
// same signature as any other argument of that parent.
#[test]
fn a_projection_below_an_inferred_parent_types() {
    let loaded = load_main(
        "inferred-parent.k",
        INFERRED_PARENT,
        "INFERRED-PARENT",
        None,
    );
    assert_compiles(&loaded, "INFERRED-PARENT");
    assert_closure_types(&loaded, "INFERRED-PARENT");
    let typing = main_typer(&loaded)
        .typing(labelled(loaded.definition(), "INFERRED-PARENT.ite"))
        .unwrap();
    assert_eq!(at(&typing, &[0, 1, 0]), &sorted(Some("Int"), Some("Int")));
    assert_eq!(
        at(&typing, &[0, 1, 0, 1]),
        &sorted(Some("Int"), Some("Int"))
    );
}

// Module B of K's issue-2114 regression sees no `K` of its own (it imports only a private module
// declaring `Foo`); compilation types its rule with the main module's order, and so does the
// main module's typer.
#[test]
fn a_sentence_whose_module_lacks_k_types_in_the_main_view() {
    let loaded = load_main(
        "issue-2114.k",
        include_str!("fixtures/sentence-typing/regression/issue-2114.k"),
        "TEST",
        None,
    );
    assert_compiles(&loaded, "issue-2114");
    let module_b = loaded
        .definition()
        .modules
        .iter()
        .find(|module| module.name == "B")
        .unwrap();
    let rule = module_b
        .local_sentences
        .iter()
        .find(|sentence| matches!(&***sentence, Sentence::Rule { .. }))
        .unwrap();
    let typing = main_typer(&loaded).typing(rule).unwrap();
    assert_eq!(at(&typing, &[0, 0]).sort, Some(Sort::new("Foo")));
    // B's own view has no `K` to join `Foo` with, so typing the rule there is not compilation's
    // typing of it.
    let own = SentenceTyper::new(loaded.resolved(), "B")
        .unwrap()
        .typing(rule)
        .unwrap_err();
    assert!(own.to_string().contains("least upper bound"), "{own}");
}

// A module that declares its own `isFoo` keeps it: the generated helpers are added only for
// labels the catalog lacks, so the typer sees one production and uses its signature. (This
// definition does not compile, since the predicate pass also declares `Bool ::= isFoo(K)` for the
// sort `Foo`; the test pins the typer's catalog, not the typing contract.)
#[test]
fn a_module_with_its_own_is_foo_keeps_it() {
    let loaded = load_main("own-predicate.k", OWN_PREDICATE, "OWN-PREDICATE", None);
    assert_closure_types(&loaded, "OWN-PREDICATE");
    let typing = main_typer(&loaded)
        .typing(labelled(loaded.definition(), "OWN-PREDICATE.use"))
        .unwrap();
    assert_eq!(at(&typing, &[0, 1, 0]), &sorted(Some("Int"), Some("Int")));
    assert_eq!(
        at(&typing, &[0, 1, 0, 0]),
        &sorted(Some("Int"), Some("Int"))
    );
}

// The rule parser refuses the text `b(isInt(X) +Int 1)`; a structured edit that puts the Bool
// predicate at `b`'s Int argument is refused by the typer with the error compilation stops at.
#[test]
fn a_structured_ill_sorted_predicate_fails_typing_and_compilation_alike() {
    let loaded = load_main(
        "generated-rule-syntax.k",
        GENERATED_RULE_SYNTAX,
        "TYPER-PROBE",
        None,
    );
    let ill_sorted = edited(
        &loaded,
        "TYPER-PROBE.field",
        &[0, 1, 0],
        Term::apply("isInt", vec![var("X", None)]),
    );
    let error = main_typer(&loaded).typing(&ill_sorted).unwrap_err();
    assert!(
        matches!(&error, SentenceTypingError::Sort { error: SortInjectionError::IllSortedTerm(mismatch), .. }
            if mismatch.found == Sort::new("Bool") && mismatch.required == Sort::new("Int")),
        "{error}"
    );
    let compiled = compiled_kore(&relinked(
        &loaded,
        "TYPER-PROBE",
        "TYPER-PROBE.field",
        ill_sorted,
    ))
    .expect_err("compilation rejects a Bool at an Int argument");
    assert_eq!(compiled.stage, "add sort injections", "{compiled}");
    let SentenceTypingError::Sort { error: typed, .. } = &error else {
        unreachable!("matched above")
    };
    assert!(
        compiled.message.contains(&typed.to_string()),
        "{compiled}\n{typed}"
    );
}

/// The definitions of the corpus property: the single-module reference fixtures, the
/// sentence-typing fixtures, and copies of K regression definitions (`pyk/regression-new`, files
/// kept byte for byte) whose rules use local functions, `:=K`, field projections, `#withConfig`
/// and a module that lacks `K`. K's withConfig2 is not among them: krust refuses its
/// fresh-variable function rule, and its own test types its `#withConfig` rule.
fn corpus() -> Vec<(String, String, String, Option<std::path::PathBuf>)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut corpus = Vec::new();
    let reference = root.join("reference");
    let mut files = std::fs::read_dir(&reference)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect::<Vec<_>>();
    files.sort();
    for path in files {
        let text = std::fs::read_to_string(&path).unwrap();
        let main = text
            .lines()
            .rev()
            .find_map(|line| line.trim_start().strip_prefix("module "))
            .unwrap()
            .trim()
            .to_owned();
        corpus.push((
            path.file_name().unwrap().to_string_lossy().into_owned(),
            text,
            main,
            Some(reference.clone()),
        ));
    }
    for (file, main) in [
        ("regression/equals-pattern.k", "TEST"),
        ("regression/let-test.k", "TEST"),
        ("regression/total-proj.k", "TEST"),
        ("regression/issue-2114.k", "TEST"),
        ("generated-rule-syntax.k", "TYPER-PROBE"),
        ("private-helpers.k", "PRIV"),
        ("inferred-parent.k", "INFERRED-PARENT"),
        ("regression/withConfig.k", "TEST"),
        ("configuration-context.k", "TYPER-CFG"),
        ("transaction-data.k", "TX-DATA"),
        ("private-configuration-context.k", "P"),
    ] {
        let path = root.join("sentence-typing").join(file);
        corpus.push((
            file.to_owned(),
            std::fs::read_to_string(&path).unwrap(),
            main.to_owned(),
            None,
        ));
    }
    corpus
}

// The typing contract: if compilation accepts a definition, every rule and claim of its main
// module's import closure (the prelude included) types with the main module's typer.
#[test]
fn every_sentence_of_a_compiled_definition_types_in_the_main_view() {
    let mut compiled = Vec::new();
    let mut failures = Vec::new();
    for (name, text, main, directory) in corpus() {
        let loaded = load_main(&name, &text, &main, directory.as_deref());
        if compile_loaded_definition(&loaded, CompileOptions::default()).is_err() {
            continue;
        }
        compiled.push(name.clone());
        let typer = main_typer(&loaded);
        for (module, sentence) in closure_sentences(&loaded) {
            if let Err(error) = typer.typing(sentence) {
                failures.push(format!("{name} {module}: {error}"));
            }
        }
    }
    // typed.k with its own prelude (portable-prelude.k), which the earlier tests load.
    let typed = load();
    assert_compiles(&typed, "TYPED");
    assert_closure_types(&typed, "TYPED");
    assert!(failures.is_empty(), "{failures:#?}");
    assert!(compiled.len() >= 29, "only {compiled:?} compiled");
    assert!(
        compiled
            .iter()
            .any(|name| name == "private-configuration-context.k"),
        "{compiled:?}"
    );
}

// An exception to the typing contract until local functions are typed as their lowering:
// compilation computes the lambda of `#let X:A = c() #in X` in B, where `D1` is the one common
// supersort of `A` and `C`; the main module adds a second, `D2`, so the main view instantiates
// the parametric `#let` ambiguously although the definition compiles.
#[test]
fn a_local_function_typed_in_the_main_view_may_fail_where_compilation_succeeds() {
    let source = r#"
module MAIN
  imports B
  syntax D2 ::= A | C
endmodule

module B
  imports INT
  imports BOOL
  syntax A ::= a()
  syntax C ::= c()
  syntax D1 ::= A | C
  syntax KItem ::= h(K) | g(K)
  rule [lam]: h(_) => g(#let X:A = c() #in X)
endmodule
"#;
    let loaded = load_main("local-function-view.k", source, "MAIN", None);
    assert_compiles(&loaded, "MAIN");
    let error = main_typer(&loaded)
        .typing(labelled(loaded.definition(), "B.lam"))
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("several incomparable least instantiations"),
        "{error}"
    );
}

// `for_compilation` is the typer of the main module.
#[test]
fn the_compilation_typer_is_the_main_modules() {
    let loaded = load_main("private-helpers.k", PRIVATE_HELPERS, "PRIV", None);
    let typer = SentenceTyper::for_compilation(loaded.resolved()).unwrap();
    let main = SentenceTyper::new(loaded.resolved(), "PRIV").unwrap();
    for (_, sentence) in closure_sentences(&loaded) {
        assert_eq!(typer.typing(sentence), main.typing(sentence));
    }
}

// The rule grammar offers the helpers of the parse-only RULE-CELLS cell sorts, but compilation
// declares helpers over the closure alone, so it has no `isGeneratedCounterCell`; neither has the
// typer.
#[test]
fn a_helper_of_a_parse_only_cell_sort_is_not_typed() {
    let loaded = load_main(
        "generated-rule-syntax.k",
        GENERATED_RULE_SYNTAX,
        "TYPER-PROBE",
        None,
    );
    let sentence = edited(
        &loaded,
        "TYPER-PROBE.pred-int",
        &[1],
        Term::apply("isGeneratedCounterCell", vec![var("X", None)]),
    );
    let error = main_typer(&loaded).typing(&sentence).unwrap_err();
    assert!(
        matches!(
            &error,
            SentenceTypingError::Sort {
                error: SortInjectionError::UnknownLabel(label),
                ..
            } if label == "isGeneratedCounterCell"
        ),
        "{error}"
    );
    assert!(
        compiled_kore(&relinked(
            &loaded,
            "TYPER-PROBE",
            "TYPER-PROBE.pred-int",
            sentence
        ))
        .is_err()
    );
}

const CONFIGURATION_CONTEXT: &str =
    include_str!("fixtures/sentence-typing/configuration-context.k");
const TRANSACTION_DATA: &str = include_str!("fixtures/sentence-typing/transaction-data.k");

// `[[ cnt() => N ]] <n> N </n>` loads as `#withConfig(cnt() => N, <n> N </n>)`: its first argument
// is the function rule, typed as a rule body, and its second the configuration context, a cell
// fragment typed as an authored cell elsewhere (at its production's sort, its body at the cell's
// content sort). The construct itself has no sort.
#[test]
fn a_function_rule_with_configuration_context_types() {
    let loaded = load_main(
        "configuration-context.k",
        CONFIGURATION_CONTEXT,
        "TYPER-CFG",
        None,
    );
    assert_compiles(&loaded, "TYPER-CFG");
    assert_closure_types(&loaded, "TYPER-CFG");
    let typing = main_typer(&loaded)
        .typing(labelled(loaded.definition(), "TYPER-CFG.withconfig"))
        .unwrap();
    assert_eq!(at(&typing, &[0]).sort, None);
    assert_eq!(at(&typing, &[0, 1]).sort, Some(Sort::new("NCell")));
    assert_eq!(at(&typing, &[0, 0]).sort, Some(Sort::new("Int")));
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(Some("Int"), Some("Int")));
    assert_eq!(at(&typing, &[0, 0, 1]), &sorted(Some("Int"), Some("Int")));
    let cell_body = typing
        .positions
        .iter()
        .filter(|(path, _)| path.starts_with(&[0, 1]) && path.len() == 3)
        .map(|(_, position)| position.clone())
        .collect::<Vec<_>>();
    assert!(
        cell_body.contains(&sorted(Some("Int"), Some("Int"))),
        "{:#?}",
        typing.positions
    );
}

// A KEVM-shaped `#getTxData` rule: several context cells, a nested cell with `...`, and a
// condition reading context variables.
#[test]
fn a_function_rule_with_nested_configuration_context_types() {
    let loaded = load_main("transaction-data.k", TRANSACTION_DATA, "TX-DATA", None);
    assert_compiles(&loaded, "TX-DATA");
    assert_closure_types(&loaded, "TX-DATA");
    let typing = main_typer(&loaded)
        .typing(labelled(loaded.definition(), "TX-DATA.tx-data"))
        .unwrap();
    assert_eq!(
        at(&typing, &[0, 0, 0]),
        &sorted(Some("TxData"), Some("TxData"))
    );
    assert_eq!(
        at(&typing, &[0, 0, 1]),
        &sorted(Some("TxData"), Some("TxData"))
    );
    assert_eq!(at(&typing, &[1]), &sorted(Some("Bool"), Some("Bool")));
}

// K's withConfig2 regression: its context is a `<k>` cell with a frame. krust refuses the
// definition for its fresh-variable function rule, so the corpus property skips it; its
// `#withConfig` rule still types as the rule compilation would lower.
#[test]
fn a_configuration_context_with_a_k_cell_frame_types() {
    let loaded = load_main(
        "withConfig2.k",
        include_str!("fixtures/sentence-typing/regression/withConfig2.k"),
        "TEST",
        None,
    );
    let typer = main_typer(&loaded);
    let with_config = closure_sentences(&loaded)
        .into_iter()
        .filter(|(module, sentence)| {
            *module == "TEST"
                && matches!(
                    sentence,
                    Sentence::Rule { body, .. }
                        if matches!(body.unannotated(), Term::Apply { label, .. } if label.name == "#withConfig")
                )
        })
        .collect::<Vec<_>>();
    assert_eq!(with_config.len(), 1);
    let typing = typer.typing(with_config[0].1).unwrap();
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(Some("Int"), Some("Int")));
    assert_eq!(at(&typing, &[0, 0, 1]), &sorted(Some("Int"), Some("Int")));
}
