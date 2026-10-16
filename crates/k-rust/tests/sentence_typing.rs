//! The public typing view of loaded rule-like sentences (`k_rust::kompile::sentence_typing`).

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Definition, ResolvedDefinition, Sentence};
use k_rust::inner::{ParseError, RuleError};
use k_rust::kast::{InternalLabel, Sort, Term};
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
                .typing_in(sentence, module)
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
        ("collection-cell-content.k", "TEST"),
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
            if let Err(error) = typer.typing_in(sentence, module) {
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

/// The signatures `(arguments, result)` of the lambda symbols of a compiled definition's KORE.
fn lambda_signatures(kore: &str) -> Vec<(Vec<String>, String)> {
    // A long declaration wraps over several lines; the parsed one is printed on one.
    let definition = k_rust::kore::parser::parse_definition(kore).expect("compiled KORE parses");
    definition
        .modules
        .into_iter()
        .flat_map(|module| module.sentences)
        .filter(|sentence| {
            matches!(sentence, k_rust::kore::ast::Sentence::SymbolDeclaration { symbol, .. }
                if symbol.name.starts_with("Lbl'Hash'lambda"))
        })
        .map(|sentence| {
            let line = k_rust::kore::printer::Printer::pretty(100_000).print_sentence(&sentence);
            let line = line.trim();
            let open = line.find("}(").expect("a symbol's argument sorts") + 2;
            let close = open
                + line[open..]
                    .find(')')
                    .expect("the end of the argument sorts");
            let arguments = line[open..close]
                .split(", ")
                .filter(|sort| !sort.is_empty())
                .map(str::to_owned)
                .collect();
            let result = line[close..]
                .trim_start_matches(") : ")
                .split_whitespace()
                .next()
                .expect("a result sort")
                .to_owned();
            (arguments, result)
        })
        .collect()
}

/// The KORE spelling `SortS{}` of the nullary sort `name`.
fn kore_name(name: &str) -> String {
    format!("Sort{name}{{}}")
}

const LAMBDA_VIEWS: &str = r#"
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

// Compilation computes the lambda of `#let X:A = c() #in X` in B, where `D1` is the one common
// supersort of `A` and `C`; the main module adds a second, `D2`. Typed in B, the module that
// declares the rule, the local function reports the lambda's sorts: the construct at its result
// `A`, the value `c()` required at its parameter `D1`.
#[test]
fn a_local_function_types_with_the_lambda_sorts_of_its_module() {
    let loaded = load_main("local-function-view.k", LAMBDA_VIEWS, "MAIN", None);
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(
        lambda_signatures(&kore),
        vec![(vec![kore_name("D1")], kore_name("A"))],
        "{kore}"
    );
    let rule = labelled(loaded.definition(), "B.lam");
    let typing = main_typer(&loaded).typing_in(rule, "B").unwrap();
    assert_eq!(at(&typing, &[0, 1, 0]).sort, Some(Sort::new("A")));
    assert_eq!(at(&typing, &[0, 1, 0, 1]), &sorted(Some("C"), Some("D1")));
    assert_eq!(at(&typing, &[0, 1, 0, 0]).required, Some(Sort::new("D1")));
    // The typer's own module is MAIN, whose order has no least upper bound of `A` and `C`; `typing`
    // computes the lambda there, and reports the parameter the lowering would give it in MAIN.
    let typing = main_typer(&loaded).typing(rule).unwrap();
    assert_eq!(
        at(&typing, &[0, 1, 0, 1]).required,
        Some(Sort::new("KItem"))
    );
}

// A lambda in B whose pattern sort `A` and argument sort `C` have no common supersort in B, while
// the main module adds `D ::= A | C`: compilation gives the lambda B's parameter, which the view
// reports, not the main module's `D`.
#[test]
fn a_lambda_signature_is_the_sentence_modules() {
    let source = r#"
module MAIN
  imports B
  syntax D ::= A | C
endmodule

module B
  imports INT
  imports BOOL
  syntax A ::= a()
  syntax C ::= c()
  syntax KItem ::= h(K) | g(K)
  rule [lam]: h(_) => g(#let X:A = c() #in X)
endmodule
"#;
    let loaded = load_main("lambda-signature.k", source, "MAIN", None);
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    let [(parameters, result)] = lambda_signatures(&kore).try_into().expect("one lambda");
    let typing = main_typer(&loaded)
        .typing_in(labelled(loaded.definition(), "B.lam"), "B")
        .unwrap();
    let parameter = at(&typing, &[0, 1, 0, 1]).required.clone().unwrap();
    assert_eq!(kore_sort(&parameter), Some(parameters[0].clone()));
    assert_ne!(parameter, Sort::new("D"));
    let sort = at(&typing, &[0, 1, 0]).sort.clone().unwrap();
    assert_eq!(kore_sort(&sort), Some(result));
}

/// The one definition `MAIN` holding `rule`, its rule's typing in MAIN, and the signature of its
/// one compiled lambda.
fn one_lambda(rule: &str) -> (SentenceTyping, (Vec<String>, String)) {
    let source = format!(
        "module MAIN\n  imports INT\n  imports BOOL\n  imports K-EQUAL\n  syntax KItem ::= h(K) | g(K) | m(Int)\n  rule [r]: {rule}\nendmodule\n"
    );
    let loaded = load_main("one-lambda.k", &source, "MAIN", None);
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{rule}: {error}"));
    let [signature] = lambda_signatures(&kore)
        .try_into()
        .unwrap_or_else(|signatures| panic!("{rule}: {signatures:?}"));
    let typing = main_typer(&loaded)
        .typing_in(labelled(loaded.definition(), "MAIN.r"), "MAIN")
        .unwrap_or_else(|error| panic!("{rule}: {error}"));
    (typing, signature)
}

// `#fun(P => B)(E)` loads as `#fun2(P => B, E)` in the Z3 build and as `#fun3(P, B, E)` in the
// portable one. Either way the pattern, the body and the value each have a position: the pattern
// and the value at the lambda's parameter, the body at its result; in the Z3 build the
// equation's rewrite has each side's typing.
#[test]
fn a_fun_with_an_inner_rewrite_types_its_pattern() {
    let (typing, (parameters, result)) = one_lambda("m(X) => g(#fun(Y => Y +Int 1)(X))");
    assert_eq!(parameters, vec![kore_name("Int")]);
    assert_eq!(result, kore_name("Int"));
    assert_eq!(at(&typing, &[0, 1, 0]).sort, Some(Sort::new("Int")));
    #[cfg(feature = "z3-inference")]
    let (pattern, body, value) = {
        // Both sides of this equation are `Int` at `Int`, so its rewrite has one typing; one
        // whose body has another sort than its pattern is typed per side.
        assert_eq!(
            at(&typing, &[0, 1, 0, 0]),
            &sorted(Some("Int"), Some("Int"))
        );
        let (typing, (parameters, result)) = one_lambda("m(X) => g(#fun(Y => Y ==Int 1)(X))");
        assert_eq!(
            (parameters, result),
            (vec![kore_name("Int")], kore_name("Bool"))
        );
        let branches = typing
            .branches
            .get(&[0, 1, 0, 0])
            .expect("the equation's rewrite");
        assert_eq!(branches.left, sorted(Some("Int"), Some("Int")));
        assert_eq!(branches.right, sorted(Some("Bool"), Some("Bool")));
        ([0, 1, 0, 0, 0], [0, 1, 0, 0, 1], [0, 1, 0, 1])
    };
    #[cfg(not(feature = "z3-inference"))]
    let (pattern, body, value) = ([0, 1, 0, 0], [0, 1, 0, 1], [0, 1, 0, 2]);
    assert_eq!(at(&typing, &pattern), &sorted(Some("Int"), Some("Int")));
    assert_eq!(at(&typing, &body), &sorted(Some("Int"), Some("Int")));
    assert_eq!(at(&typing, &value), &sorted(Some("Int"), Some("Int")));
}

// The lambda of `#let` and of `#fun` with a sorted pattern: the construct at the compiled
// lambda's result sort, the value required at its parameter sort.
#[test]
fn let_and_fun_positions_are_the_lowering_sorts() {
    for (rule, construct, value) in [
        (
            "m(X) => g(#let Y = X #in Y +Int 1)",
            [0, 1, 0].as_slice(),
            [0, 1, 0, 1].as_slice(),
        ),
        (
            "m(X) => g(#fun(Y:Int => Y +Int 1)(X))",
            &[0, 1, 0],
            if cfg!(feature = "z3-inference") {
                &[0, 1, 0, 1]
            } else {
                &[0, 1, 0, 2]
            },
        ),
        ("h(X) => g(#let Y = X #in Y)", &[0, 1, 0], &[0, 1, 0, 1]),
    ] {
        let (typing, (parameters, result)) = one_lambda(rule);
        let reported = at(&typing, construct).sort.clone().unwrap();
        assert_eq!(kore_sort(&reported), Some(result), "{rule}");
        let required = at(&typing, value).required.clone().unwrap();
        assert_eq!(kore_sort(&required), Some(parameters[0].clone()), "{rule}");
    }
}

// `P :=K E` is a predicate: a Bool condition whose value is required at the lambda's parameter.
#[test]
fn a_match_reports_bool() {
    let (typing, (parameters, result)) = one_lambda("m(X) => g(0) requires X :=K 0");
    assert_eq!(result, kore_name("Bool"));
    assert_eq!(at(&typing, &[1]), &sorted(Some("Bool"), Some("Bool")));
    let required = at(&typing, &[1, 1]).required.clone().unwrap();
    assert_eq!(kore_sort(&required), Some(parameters[0].clone()));
    assert_eq!(at(&typing, &[1, 0]).required, Some(required));
}

// A local function in the body of another is its own scope: both are typed as their lambdas.
#[test]
fn a_nested_local_function_types() {
    let source = "module MAIN\n  imports INT\n  syntax KItem ::= m(Int) | g(K)\n  rule [r]: m(X) => g(#let Y = X #in #let Z = Y #in Z +Int 1)\nendmodule\n";
    let loaded = load_main("nested.k", source, "MAIN", None);
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    // Both patterns are unsorted variables, so both lambdas take `K`, and both bodies are `Int`.
    assert_eq!(
        lambda_signatures(&kore),
        vec![(vec![kore_name("K")], kore_name("Int")); 2],
        "{kore}"
    );
    let typing = main_typer(&loaded)
        .typing_in(labelled(loaded.definition(), "MAIN.r"), "MAIN")
        .unwrap();
    // The outer construct and the inner one (the outer body) at the result, their values `X`
    // and `Y` at the parameter, the inner body `Z +Int 1` at `Int`.
    for (path, sort, required) in [
        ([0, 1, 0].as_slice(), Some("Int"), None),
        (&[0, 1, 0, 1], None, Some("K")),
        (&[0, 1, 0, 2], Some("Int"), None),
        (&[0, 1, 0, 2, 1], None, Some("K")),
        (&[0, 1, 0, 2, 2], Some("Int"), None),
    ] {
        let position = at(&typing, path);
        if let Some(sort) = sort {
            assert_eq!(position.sort, Some(Sort::new(sort)), "{path:?}");
        }
        if let Some(required) = required {
            assert_eq!(position.required, Some(Sort::new(required)), "{path:?}");
        }
    }
}

// The rule parser gives one variable one sort across a rule, but a structured edit can bind a
// pattern variable that shadows an enclosing one with another sort. Compilation lowers the local
// function before it resolves semantic casts, so the generated equation's `X:Bool` and the
// enclosing rule's `X:Int` are resolved apart; the view resolves them in the same scopes.
#[test]
fn a_pattern_variable_that_shadows_an_enclosing_one_is_resolved_in_its_own_scope() {
    let source = "module MAIN\n  imports INT\n  imports BOOL\n  syntax KItem ::= h(K) | g(K)\n  rule [r]: h(Y) => g(#let X = 1 #in Y)\nendmodule\n";
    let loaded = load_main("shadow.k", source, "MAIN", None);
    let original = labelled(loaded.definition(), "MAIN.r").clone();
    let Sentence::Rule { body, .. } = &original else {
        panic!("a rule")
    };
    let Term::Rewrite { left, right } = body.unannotated() else {
        panic!("{body}")
    };
    let (Term::Apply { label: h, .. }, Term::Apply { label: g, .. }) =
        (left.unannotated(), right.unannotated())
    else {
        panic!("{body}")
    };
    let truth = Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let shadowing = edited(
        &loaded,
        "MAIN.r",
        &[0],
        rewrite(
            Term::Apply {
                label: h.clone(),
                arguments: vec![cast("Int", var("X", None))],
            },
            Term::Apply {
                label: g.clone(),
                arguments: vec![Term::apply(
                    "#let",
                    vec![cast("Bool", var("X", None)), truth, var("X", None)],
                )],
            },
        ),
    );
    let relinked = relinked(&loaded, "MAIN", "MAIN.r", shadowing.clone());
    let kore = compiled_kore(&relinked).unwrap_or_else(|error| panic!("{error}"));
    let typing = main_typer(&relinked)
        .typing_in(&shadowing, "MAIN")
        .unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(
        lambda_signatures(&kore),
        vec![(vec![kore_name("Bool")], kore_name("K"))]
    );
    // `X` is an `Int` in the enclosing rule, a `Bool` in the equation; the unsorted body `X`
    // gives the lambda the result `K`.
    assert_eq!(at(&typing, &[0, 0, 0]).sort, Some(Sort::new("Int")));
    assert_eq!(at(&typing, &[0, 1, 0]).sort, Some(Sort::new("K")));
    assert_eq!(
        at(&typing, &[0, 1, 0, 0]),
        &sorted(Some("Bool"), Some("Bool"))
    );
    assert_eq!(at(&typing, &[0, 1, 0, 2]).sort, Some(Sort::new("Bool")));
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

// The typer is `Send`: a consumer may build it once and type on a worker thread.
const _: fn() = || {
    fn send<T: Send>() {}
    send::<SentenceTyper<'static>>();
};

/// `rules` as the module `MAIN` over `h(K)`, `g(K)`, `m(Int)` and the sorts `A`, `C` with two
/// common supersorts `D1` and `D2`: every rule that compiles types with `typing_in` in `MAIN`,
/// each local function at its compiled lambda's result sort.
fn assert_rules_type_as_compiled(rules: &[(&str, &str)]) {
    let source = format!(
        "module MAIN\n  imports INT\n  imports BOOL\n  syntax A ::= a()\n  syntax C ::= c()\n  \
         syntax D1 ::= A | C\n  syntax D2 ::= A | C\n  \
         syntax KItem ::= h(K) | g(K) | m(Int) | w(KItem)\n  {}\nendmodule\n",
        rules
            .iter()
            .map(|(label, rule)| format!("rule [{label}]: {rule}"))
            .collect::<Vec<_>>()
            .join("\n  ")
    );
    let loaded = load_main("local-function-shapes.k", &source, "MAIN", None);
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    assert_eq!(lambda_signatures(&kore).len(), rules.len(), "{kore}");
    let typer = main_typer(&loaded);
    for (label, rule) in rules {
        typer
            .typing_in(
                labelled(loaded.definition(), &format!("MAIN.{label}")),
                "MAIN",
            )
            .unwrap_or_else(|error| panic!("{rule}: {error}"));
    }
}

// A semantic cast around a local function: resolution puts the cast's sort on the stand-in for
// the construct, and the typer types the construct below the cast.
#[test]
fn a_local_function_under_a_semantic_cast_types() {
    assert_rules_type_as_compiled(&[
        ("r", "h(_) => g((#let X:Int = 1 #in X +Int 1):Int)"),
        ("s", "h(_) => m((#let X = 1 #in X):Int)"),
        (
            "t",
            "h(Y) => g(Y) requires (#let X:Int = 1 #in X >Int 0):Bool",
        ),
    ]);
}

// A structured cast around a local function that compilation refuses (`Int` cast to `Bool`) or
// accepts (`Int` cast to `KItem`): the typer reports an error exactly where compilation does,
// and never panics.
#[test]
fn a_structured_cast_around_a_local_function_types_as_compilation_does() {
    let source = "module MAIN\n  imports INT\n  imports BOOL\n  syntax KItem ::= h(K) | g(K)\n  rule [r]: h(_) => g(#let X:Int = 1 #in X +Int 1)\nendmodule\n";
    let loaded = load_main("cast-local-function.k", source, "MAIN", None);
    for sort in ["Bool", "KItem", "Int"] {
        let original = labelled(loaded.definition(), "MAIN.r").clone();
        let Sentence::Rule { body, .. } = &original else {
            panic!("a rule")
        };
        let Term::Rewrite { right, .. } = body.unannotated() else {
            panic!("{body}")
        };
        let Term::Apply { arguments, .. } = right.unannotated() else {
            panic!("{body}")
        };
        let cast_let = cast(sort, arguments[0].clone());
        let sentence = edited(&loaded, "MAIN.r", &[0, 1, 0], cast_let);
        let compiled = compiled_kore(&relinked(&loaded, "MAIN", "MAIN.r", sentence.clone()));
        let typed = main_typer(&loaded).typing_in(&sentence, "MAIN");
        assert_eq!(
            typed.is_ok(),
            compiled.is_ok(),
            "{sort}: typing {typed:?}, compilation {:?}",
            compiled.as_ref().map(|_| ()).map_err(ToString::to_string)
        );
    }
}

// A `#fun` whose rewrite lies below the top of its equation, `#fun(w(_:A => c()))(X)`: the
// lowering's pattern and body are the equation's left and right projections, `w(_:A)` and
// `w(c())`, each typed alone, so `A` and `C` are never joined (they have two least upper
// bounds here). The portable rule grammar reads the text; the Z3 one does not, and the
// structured `#fun2` takes the same path.
#[test]
fn a_rewrite_below_the_top_of_a_fun_equation_is_typed_per_projection() {
    #[cfg(not(feature = "z3-inference"))]
    assert_rules_type_as_compiled(&[("r", "h(X) => g(#fun(w(_:A => c()))(X))")]);
    let source = "module MAIN\n  imports INT\n  imports BOOL\n  syntax A ::= a()\n  syntax C ::= c()\n  syntax D1 ::= A | C\n  syntax D2 ::= A | C\n  syntax KItem ::= h(K) | g(K) | w(KItem)\n  rule [r]: h(X) => g(X)\nendmodule\n";
    let loaded = load_main("nested-equation.k", source, "MAIN", None);
    let original = labelled(loaded.definition(), "MAIN.r").clone();
    let Sentence::Rule { body, .. } = &original else {
        panic!("a rule")
    };
    let Term::Rewrite { left, right } = body.unannotated() else {
        panic!("{body}")
    };
    let (
        Term::Apply {
            label: h,
            arguments: h_arguments,
        },
        Term::Apply { label: g, .. },
    ) = (left.unannotated(), right.unannotated())
    else {
        panic!("{body}")
    };
    let label_of = |prefix: &str| {
        loaded
            .definition()
            .modules
            .iter()
            .find(|module| module.name == "MAIN")
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label), ..
                } if label.name.starts_with(prefix) => Some(label.clone()),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no production {prefix}"))
    };
    let w = label_of("w(");
    let c = Term::Apply {
        label: label_of("c("),
        arguments: Vec::new(),
    };
    let x = h_arguments[0].clone();
    let equation = Term::Apply {
        label: w,
        arguments: vec![rewrite(cast("A", var("_Y", None)), c)],
    };
    let sentence = edited(
        &loaded,
        "MAIN.r",
        &[0],
        rewrite(
            Term::Apply {
                label: h.clone(),
                arguments: vec![x.clone()],
            },
            Term::Apply {
                label: g.clone(),
                arguments: vec![Term::apply("#fun2", vec![equation, x])],
            },
        ),
    );
    let compiled = compiled_kore(&relinked(&loaded, "MAIN", "MAIN.r", sentence.clone()));
    let typed = main_typer(&loaded).typing_in(&sentence, "MAIN");
    assert!(
        compiled.is_ok() && typed.is_ok(),
        "typing {typed:?}, compilation {:?}",
        compiled.as_ref().map(|_| ()).map_err(ToString::to_string)
    );
    let typing = typed.unwrap();
    // The equation `w(_:A => c())` at [0, 1, 0, 0] is `w(_:A)` on the left and `w(c())` on the
    // right; the rewrite below it is `A` on the left and `C` on the right.
    assert!(
        typing.branches.get(&[0, 1, 0, 0, 0]).is_some(),
        "{:#?}",
        typing.branches
    );
}

// ---------------------------------------------------------------------------------------------
// Cell-fragment variables: the sorts cell completion gives them.

const COLLECTION_CELL_CONTENT: &str =
    include_str!("fixtures/sentence-typing/collection-cell-content.k");

/// The path of every named variable of `sentence`, a rule or claim, with its name: the paths of
/// [`SentenceTyping`], a semantic cast being an application. A local function's equation is a
/// rule of its own once compiled, and only its value is walked.
fn named_variables(sentence: &Sentence) -> Vec<(Vec<u32>, String)> {
    fn walk(term: &Term, path: &mut Vec<u32>, found: &mut Vec<(Vec<u32>, String)>) {
        if let Term::Apply { label, arguments } = term.unannotated() {
            let value = match arguments.len() {
                3 if label.is(InternalLabel::Let) => Some(1),
                3 if label.is(InternalLabel::Fun3) => Some(2),
                2 if label.is(InternalLabel::Fun2) => Some(1),
                _ => None,
            };
            if let Some(value) = value {
                path.push(value);
                walk(&arguments[value as usize], path, found);
                path.pop();
                return;
            }
        }
        let children: Vec<&Term> = match term.unannotated() {
            Term::Variable { name, .. } => {
                if !name.starts_with('_') {
                    found.push((path.clone(), name.clone()));
                }
                return;
            }
            Term::Rewrite { left, right } => vec![left, right],
            Term::As { pattern, alias } => vec![pattern, alias],
            Term::Apply { arguments, .. } => arguments.iter().collect(),
            Term::Sequence(items) => items.iter().collect(),
            _ => return,
        };
        for (index, child) in children.into_iter().enumerate() {
            path.push(u32::try_from(index).unwrap());
            walk(child, path, found);
            path.pop();
        }
    }
    let (Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    }
    | Sentence::Claim {
        body,
        requires,
        ensures,
        ..
    }) = sentence
    else {
        panic!("a rule or claim")
    };
    let mut found = Vec::new();
    for (field, root) in [body, requires, ensures].into_iter().enumerate() {
        walk(root, &mut vec![u32::try_from(field).unwrap()], &mut found);
    }
    found
}

/// The subterm of `sentence`, a rule or claim, at `path`.
fn subterm<'a>(sentence: &'a Sentence, path: &[u32]) -> &'a Term {
    let (Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    }
    | Sentence::Claim {
        body,
        requires,
        ensures,
        ..
    }) = sentence
    else {
        panic!("a rule or claim")
    };
    let mut term = [body, requires, ensures][path[0] as usize];
    for step in &path[1..] {
        let step = *step as usize;
        term = match term.unannotated() {
            Term::Rewrite { left, right } => [left, right][step],
            Term::As { pattern, alias } => [pattern, alias][step],
            Term::Apply { arguments, .. } => &arguments[step],
            Term::Sequence(items) => &items[step],
            other => panic!("no child {step} in {other}"),
        };
    }
    term
}

/// The typings of `path`: its one position, or its position in each branch.
fn typings_at<'a>(typing: &'a SentenceTyping, path: &[u32]) -> Vec<&'a PositionTyping> {
    match typing.positions.get(path) {
        Some(position) => vec![position],
        None => typing
            .branches
            .get(path)
            .map(|branches| vec![&branches.left, &branches.right])
            .unwrap_or_else(|| panic!("no typing of {path:?}")),
    }
}

/// The text of the axiom or claim that carries `label`, from its `axiom{` or `claim{` up to
/// the label attribute.
fn sentence_of<'a>(kore: &'a str, label: &str) -> &'a str {
    let attribute = format!("label{{}}(\"{label}\")");
    let end = kore
        .find(&attribute)
        .unwrap_or_else(|| panic!("no sentence labelled {label}"));
    let start = ["axiom{", "claim{"]
        .iter()
        .filter_map(|keyword| kore[..end].rfind(keyword))
        .max()
        .expect("a sentence precedes its attributes");
    &kore[start..end]
}

/// For every labelled rule and claim of `module`, the view's sort of each occurrence of a named
/// variable is the sort of the term the compiled sentence `kore` has for it: the variable at
/// that sort, the fragment term of that sort (`<p>-fragment(..)`, injected at the position), or,
/// for an occurrence the view reports no sort for, no such variable at all (completion replaced
/// it by its parts). The operand of a cast to `Bag`, which cell completion removes, reports the
/// requirement of the cast's position. Returns the number of occurrences checked.
fn assert_variable_sorts_are_compiled(
    loaded: &LoadedDefinition,
    module: &str,
    kore: &str,
) -> usize {
    let typer = main_typer(loaded);
    let mut checked = 0;
    let sentences = loaded
        .definition()
        .modules
        .iter()
        .find(|candidate| candidate.name == module)
        .unwrap()
        .local_sentences
        .iter();
    for sentence in sentences {
        if !matches!(&**sentence, Sentence::Rule { .. } | Sentence::Claim { .. }) {
            continue;
        }
        let Some(label) = sentence.attributes().string(AttributeKey::Label) else {
            continue;
        };
        let compiled = sentence_of(kore, label);
        let typing = typer
            .typing_in(sentence, module)
            .unwrap_or_else(|error| panic!("{label}: {error}"));
        for (path, name) in named_variables(sentence) {
            for position in typings_at(&typing, &path) {
                match &position.sort {
                    Some(sort) if sort.name.ends_with("CellFragment") => assert!(
                        compiled.contains(&format!("Sort{}{{}}", sort.name))
                            && compiled.contains("'-fragment{}("),
                        "{label}: {name} at {path:?} is a {sort}, which {compiled} does not build"
                    ),
                    Some(sort) => assert!(
                        compiled.contains(&format!("Var{name}:Sort{}{{}}", sort.name)),
                        "{label}: {name} at {path:?} is a {sort}, unlike {compiled}"
                    ),
                    None => assert!(
                        !compiled.contains(&format!("Var{name}:")),
                        "{label}: {name} at {path:?} has no sort, unlike {compiled}"
                    ),
                }
                let (_, parent) = path.split_last().unwrap();
                if matches!(
                    subterm(sentence, parent).unannotated(),
                    Term::Apply { label, .. } if label.semantic_cast_sort() == Some(Sort::new("Bag"))
                ) {
                    let cast = typings_at(&typing, parent);
                    assert!(
                        cast.iter().any(|cast| cast.required == position.required)
                            && position.required != Some(Sort::new("Bag")),
                        "{label}: {name} at {path:?} requires {:?}, its cast's position {cast:?}",
                        position.required
                    );
                }
                checked += 1;
            }
        }
    }
    checked
}

/// The positions of `typing` at the occurrences of `name` in `sentence`, by path.
fn occurrences<'a>(
    typing: &'a SentenceTyping,
    sentence: &Sentence,
    name: &str,
) -> Vec<(Vec<u32>, &'a PositionTyping)> {
    named_variables(sentence)
        .into_iter()
        .filter(|(_, variable)| variable == name)
        .flat_map(|(path, _)| {
            typings_at(typing, &path)
                .into_iter()
                .map(move |position| (path.clone(), position))
        })
        .collect()
}

/// The sorts the view gives the occurrences of `name` in the rule labelled `label`.
fn occurrence_sorts(loaded: &LoadedDefinition, label: &str, name: &str) -> Vec<Option<String>> {
    let sentence = labelled(loaded.definition(), label);
    let typing = main_typer(loaded).typing_in(sentence, "TEST").unwrap();
    let mut sorts = occurrences(&typing, sentence, name)
        .into_iter()
        .map(|(_, position)| position.sort.as_ref().map(ToString::to_string))
        .collect::<Vec<_>>();
    sorts.sort();
    sorts.dedup();
    sorts
}

// A variable without a cell sort written in the body of a cell with children is a cell
// fragment: completion places it, at that occurrence, in the children it stands for (at a
// collection's sort for a `multiplicity="*"` child, a cell's sort for another, nothing for none
// or several), and replaces every other occurrence by the cell's fragment term. The rule parser
// reads it at `Bag`. KEVM's `#pushWorldState` and KWasm's
// `<moduleInstances> _ => .Bag </moduleInstances>` have such variables.
#[test]
fn a_cell_fragment_variable_has_the_sorts_cell_completion_gives_it() {
    let loaded = load_main(
        "collection-cell-content.k",
        COLLECTION_CELL_CONTENT,
        "TEST",
        None,
    );
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    assert!(assert_closure_types(&loaded, "TEST") > 0);
    assert!(assert_view_injections_are_emitted(&loaded, "TEST") > 0);
    assert!(assert_variable_sorts_are_compiled(&loaded, "TEST", &kore) > 0);
    let sorts = |label: &str, name: &str| occurrence_sorts(&loaded, &format!("TEST.{label}"), name);
    let some = |sorts: &[&str]| {
        sorts
            .iter()
            .map(|sort| Some((*sort).to_owned()))
            .collect::<Vec<_>>()
    };
    // A collection child, through a rewrite side and inside a cell under a constructor.
    assert_eq!(sorts("save", "A"), some(&["AccountCellMap"]));
    assert_eq!(sorts("restore", "A"), some(&["AccountCellMap"]));
    // The other occurrences are the fragment term, in the body and in the requires.
    assert_eq!(
        sorts("keep-queue", "Q"),
        some(&["ItemCellList", "QueueCellFragment"])
    );
    assert_eq!(
        sorts("keep-accounts", "A"),
        some(&["AccountCellMap", "AccountsCellFragment"])
    );
    assert_eq!(
        sorts("checked", "A"),
        some(&["AccountCellMap", "AccountsCellFragment"])
    );
    assert_eq!(
        sorts("boxed", "A"),
        some(&["AccountCellMap", "AccountsCellFragment"])
    );
    assert_eq!(
        sorts("cast-fragment", "A"),
        some(&["AccountCellMap", "AccountsCellFragment"])
    );
    assert_eq!(
        sorts("let", "A"),
        some(&["AccountCellMap", "AccountsCellFragment"])
    );
    // A single child, a `?` child, an annotation `X:Bag`, among several items.
    assert_eq!(
        sorts("keep-one", "X"),
        some(&["InnerCell", "OneCellFragment"])
    );
    assert_eq!(sorts("drop-maybe", "X"), some(&["MaybeCell"]));
    assert_eq!(sorts("cast-bag", "X"), some(&["AccountCellMap"]));
    assert_eq!(sorts("mixed", "A"), some(&["AccountCellMap"]));
    // The one free child of a cell with several children.
    assert_eq!(sorts("two", "A"), some(&["Acc2CellMap", "TwoCellFragment"]));
    assert_eq!(
        sorts("pair-read", "P"),
        some(&["PairCellFragment", "RCell"])
    );
    // A variable for two children or none has no one term in the body.
    assert_eq!(
        sorts("pair", "P"),
        vec![None, Some("PairCellFragment".to_owned())]
    );
    assert_eq!(
        sorts("zero-one", "X"),
        vec![None, Some("OneCellFragment".to_owned())]
    );
    // The sort predicate of the variable tests its one part.
    assert_eq!(sorts("tested", "A"), some(&["AccountCellMap"]));
    // A local function's value is a term of the sentence's scope; a closure variable is
    // written only in the equation, whose occurrences the helper does not walk, and its
    // fragment term fits the parameter sort `AccountsCellFragment` the equation gives it.
    assert_eq!(sorts("closure", "A"), some(&["AccountCellMap"]));
    assert_eq!(sorts("value-cell", "A"), some(&["AccountCellMap"]));
    assert_eq!(
        sorts("applied", "A"),
        some(&["AccountCellMap", "AccountsCellFragment"])
    );
    // The alias of one cell has that cell's sort wherever it occurs.
    assert_eq!(sorts("aliased", "X"), some(&["AccountCell"]));
    // A variable of a cell sort is an item, not a fragment, wherever it occurs.
    assert_eq!(sorts("one-account", "X"), some(&["AccountCell"]));
    assert_eq!(sorts("map-annotated", "A"), some(&["AccountCell"]));
    // `variables` has the sort the compiled variable has, and nothing for a variable that
    // completion splits.
    let typer = main_typer(&loaded);
    let typing = |label: &str| {
        typer
            .typing_in(
                labelled(loaded.definition(), &format!("TEST.{label}")),
                "TEST",
            )
            .unwrap()
    };
    assert_eq!(
        typing("keep-queue").variables.get("Q"),
        Some(&Sort::new("ItemCellList"))
    );
    assert_eq!(typing("pair").variables.get("P"), None);
    assert_eq!(
        typing("aliased").variables.get("X"),
        Some(&Sort::new("AccountCell"))
    );
}

/// `rule` added to the collection-cell-content fixture, loaded.
fn with_rule(rule: &str) -> LoadedDefinition {
    let source =
        COLLECTION_CELL_CONTENT.replace("endmodule", &format!("  rule [probe]: {rule}\nendmodule"));
    load_main("collection-cell-content.k", &source, "TEST", None)
}

// Each of these rules is rejected by compilation, and so its typing fails, with the reason
// compilation gives. Before the typer modelled the fragment term, it typed the other occurrence
// at `Bag` and accepted the first six.
#[test]
fn a_cell_fragment_sentence_compilation_rejects_fails_typing() {
    for (rule, reason) in [
        (
            "<k> go => fooBag(A) ... </k> <accounts> A </accounts>",
            "AccountsCellFragment",
        ),
        (
            "<k> go => .K ... </k> <accounts> A </accounts> requires pb(A)",
            "AccountsCellFragment",
        ),
        (
            "<k> fooBag(M) => .K ... </k> <accounts> _ => M:Bag </accounts>",
            "AccountsCellFragment",
        ),
        (
            "<k> go => fooBag(T) ... </k> <tags> T </tags>",
            "TagsCellFragment",
        ),
        (
            "<k> go => fooBag(X) ... </k> <one> X </one>",
            "OneCellFragment",
        ),
        (
            "<k> go => fooBag(A) ... </k> <two> A <cnt> C </cnt> </two>",
            "TwoCellFragment",
        ),
        (
            "<k> go => .K ... </k> <accounts> A </accounts> <tags> A </tags>",
            "is used under two cells",
        ),
        (
            "<k> go => fooK(REST) ... </k> <account> <id> 1 </id> REST ... </account>",
            "as can the frame",
        ),
        // A closure variable is passed to the lambda as its fragment term, at the parameter
        // sort its occurrence in the equation gives it (`Bag` here).
        (
            "<k> go => #let Y = 1 #in fooK(A) ... </k> <accounts> A </accounts>",
            "AccountsCellFragment",
        ),
        // An alias closure variable is passed at its cell's sort, here to a `Bag` parameter.
        (
            "<k> go => #let Y = 1 #in fooK(X) ... </k> <one> (<inner> 1 </inner> #as X) </one>",
            "term X has sort InnerCell, which is not a subsort of the sort Bag",
        ),
        // Completion places no local function in a cell body; the view refuses the shape.
        (
            "<k> go => .K ... </k> <accounts> _ => #let Y = 1 #in A </accounts> <tags> A </tags>",
            "cannot place",
        ),
    ] {
        let loaded = with_rule(rule);
        let compiled = compiled_kore(&loaded)
            .err()
            .unwrap_or_else(|| panic!("{rule}: compiles"));
        assert!(
            compiled.to_string().contains(reason)
                || compiled
                    .diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.message.contains(reason)),
            "{rule}: {compiled} {:?}",
            compiled.diagnostics
        );
        let error = main_typer(&loaded)
            .typing_in(labelled(loaded.definition(), "TEST.probe"), "TEST")
            .err()
            .unwrap_or_else(|| panic!("{rule}: types"));
        assert!(error.to_string().contains(reason), "{rule}: {error}");
    }
}

/// The typing of the rule `TEST.probe` of `loaded`, in the main view.
fn probe_typing(loaded: &LoadedDefinition) -> Result<SentenceTyping, SentenceTypingError> {
    main_typer(loaded).typing_in(labelled(loaded.definition(), "TEST.probe"), "TEST")
}

// A local function's equation is a scope of its own: a variable its pattern binds is not the
// enclosing cell-fragment variable of the same name, and these rules compile and type.
#[test]
fn a_local_functions_own_variable_is_no_cell_fragment() {
    for rule in [
        "<k> go => #fun(A => fooK(A))(1) ... </k> <accounts> A </accounts>",
        "<k> go => #let A = 1 #in fooK(A) ... </k> <accounts> A </accounts>",
    ] {
        let loaded = with_rule(rule);
        compiled_kore(&loaded).unwrap_or_else(|error| panic!("{rule}: {error}"));
        let typing = probe_typing(&loaded).unwrap_or_else(|error| panic!("{rule}: {error}"));
        assert_eq!(
            typing.variables.get("A"),
            Some(&Sort::new("AccountCellMap")),
            "{rule}"
        );
    }
}

// The stated exception to compiles-implies-types: compilation completes the cells of a local
// function's equation as a rule of its own, which the view does not, so it refuses an equation
// with a variable in the body of a cell with children, although compilation accepts it.
#[test]
fn a_cell_with_a_variable_in_a_local_functions_equation_is_refused() {
    let loaded = with_rule(
        "<k> go => #fun(box(<accounts> B </accounts>) => fooK(B))(box(<accounts> A </accounts>)) ... </k> <accounts> A </accounts>",
    );
    compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    let error = probe_typing(&loaded).unwrap_err();
    assert!(
        matches!(error, SentenceTypingError::CellCompletion { .. })
            && error.to_string().contains("equation of a local function"),
        "{error}"
    );
}

// Macro expansion reads instances from a typing without the cell-completion re-sorting, so what
// compiles is what compiled before the view modelled it. With it, `m(A)` beside
// `<two> A <cnt> C </cnt> </two>` would have the instance `TwoCellFragment` instead of `Bag`, and
// `mm()` beside `<accounts> A </accounts>` would have a known instance instead of none.
#[test]
fn macro_expansion_compiles_as_without_the_cell_completion_view() {
    let loaded = load_main(
        "macro-instance-fragment.k",
        include_str!("fixtures/sentence-typing/macro-instance-fragment.k"),
        "TEST",
        None,
    );
    let kore = compiled_kore(&loaded).unwrap_or_else(|error| panic!("{error}"));
    let axiom = sentence_of(&kore, "TEST.r");
    let axiom = &axiom[..axiom.rfind("\n    [").expect("the axiom has attributes")];
    assert_eq!(
        format!("{}\n", axiom.trim_end()),
        include_str!("fixtures/sentence-typing/macro-instance-fragment.axiom")
    );
    // `mm()` beside a sentence the view without the model does not type (a fragment variable
    // at `Bag` in an `AccountCellMap` body, an as-pattern of an authored cell) has no instance.
    for (name, source) in [
        (
            "macro-instance-undetermined.k",
            include_str!("fixtures/sentence-typing/macro-instance-undetermined.k"),
        ),
        (
            "macro-instance-alias-one.k",
            include_str!("fixtures/sentence-typing/macro-instance-alias-one.k"),
        ),
        (
            "macro-instance-alias-accounts.k",
            include_str!("fixtures/sentence-typing/macro-instance-alias-accounts.k"),
        ),
    ] {
        let loaded = load_main(name, source, "TEST", None);
        let error = compiled_kore(&loaded).unwrap_err();
        assert!(
            error.diagnostics.iter().any(|diagnostic| diagnostic
                .message
                .contains("macro symbol that was not expanded")),
            "{name}: {error} {:?}",
            error.diagnostics
        );
    }
}

// The rule parser reads no collection-sorted variable as a cell's content.
#[test]
fn a_collection_sorted_variable_is_no_cell_content() {
    let source = COLLECTION_CELL_CONTENT.replace(
        "endmodule",
        "  rule [probe]: <k> go => .K ... </k> <accounts> X:AccountCellMap </accounts>\nendmodule",
    );
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let loaded = load_for_compilation(
        ResolvedSource::new("collection-cell-content.k", source),
        "TEST",
        None,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![
                builtin::embedded("kast.md").unwrap(),
                builtin::embedded("prelude.md").unwrap(),
            ],
            ..LoadOptions::default()
        },
    );
    let Err(error) = loaded else {
        panic!("the rule parses")
    };
    assert!(error.to_string().contains(":AccountCellMap"), "{error}");
}

// A claim's cell-fragment variables are completed as a rule's are.
#[test]
fn a_claims_cell_fragment_variable_has_the_sorts_cell_completion_gives_it() {
    let source = format!(
        "{COLLECTION_CELL_CONTENT}\nmodule SPEC\n  imports TEST\n  \
         claim [claim-accounts]: <k> keepAccounts => fooK(A) ... </k> <accounts> A => .Bag </accounts>\n  \
         claim [claim-pair]: <k> pair => fooK(P) ... </k> <pair> P </pair>\nendmodule\n"
    );
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new("collection-cell-content-spec.k", source),
        "SPEC",
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
            configuration_module: Some("TEST".into()),
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{error}"));
    let kore = compile_loaded_definition(
        &loaded,
        CompileOptions {
            check_mode: k_rust::definition::CheckMode::Proof {
                definition_module: "TEST".into(),
            },
            default_claims_to_all_path: true,
            ..CompileOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{error} {:?}", error.diagnostics))
    .definition_kore;
    assert!(assert_closure_types(&loaded, "SPEC") > 0);
    assert!(assert_variable_sorts_are_compiled(&loaded, "SPEC", &kore) > 0);
    let typer = main_typer(&loaded);
    let claim = labelled(loaded.definition(), "SPEC.claim-accounts");
    let typing = typer.typing_in(claim, "SPEC").unwrap();
    let mut sorts = occurrences(&typing, claim, "A")
        .into_iter()
        .map(|(_, position)| position.sort.clone())
        .collect::<Vec<_>>();
    sorts.sort();
    sorts.dedup();
    assert_eq!(
        sorts,
        vec![
            Some(Sort::new("AccountCellMap")),
            Some(Sort::new("AccountsCellFragment"))
        ]
    );
}
