//! The public typing view of loaded rule-like sentences (`k_rust::kompile::sentence_typing`).

use k_rust::builtin;
use k_rust::definition::{AttributeKey, Definition, ResolvedDefinition, Sentence};
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
    let typing = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap();

    assert_eq!(
        typing.branches.get(&vec![0]),
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
    let mut definition = loaded.definition.clone();
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
    LoadedDefinition {
        files: loaded.files.clone(),
        source_table: loaded.source_table.clone(),
        resolved: k_rust::definition::ResolvedDefinition::resolve(&definition).unwrap(),
        definition,
        diagnostics: loaded.diagnostics.clone(),
    }
}

fn compiled_kore(loaded: &LoadedDefinition) -> Result<String, k_rust::kompile::CompileError> {
    compile_loaded_definition(loaded, CompileOptions::default())
        .map(|artifacts| artifacts.definition_kore)
}

fn lowered(source: &str) -> (Definition, ResolvedDefinition) {
    let parsed = k_rust::outer::parse("lowered.k", source).expect("definition should parse");
    let definition = k_rust::outer::lower(&parsed, "MAIN").expect("definition should lower");
    let definition =
        k_rust::inner::resolve_rule_bubbles(&definition).expect("rule bubbles should resolve");
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

#[test]
fn a_user_sort_above_k_is_circular() {
    let (_, resolved) = lowered(indoc::indoc! {r#"
        module MAIN
          syntax K
          syntax KItem
          syntax K ::= KItem
          syntax Above ::= K
        endmodule
    "#});
    assert!(matches!(
        SentenceTyper::new(&resolved, "MAIN"),
        Err(SentenceTypingError::Sort {
            error: SortInjectionError::CircularSubsort(_),
            ..
        })
    ));
}

// A cast on an as-pattern fixes the sort both sides are placed at, before any least upper bound:
// `#SemanticCastToBool(z #as B:Bool)` places `z:Nat` at `Bool`, which compilation rejects.
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
    let error = sentence_typing(&loaded.resolved, "TYPED", &ill_sorted).unwrap_err();
    assert!(
        matches!(&error, SentenceTypingError::Sort { error: SortInjectionError::IllSortedTerm(mismatch), .. }
            if mismatch.found == Sort::new("Nat") && mismatch.required == Sort::new("Bool")),
        "{error}"
    );
    let compiled = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.branch", ill_sorted));
    assert!(compiled.is_err());

    // `#SemanticCastToKItem(counter(..) #as _C:Counter)` as the left side: both sides at KItem.
    let mut sentence = labelled(&loaded.definition, "TYPED.increment").clone();
    let left = term_at(&mut sentence, &[0, 0]).clone();
    *term_at(&mut sentence, &[0, 0]) = cast("KItem", as_pattern(left, var("_C", Some("Counter"))));
    let typing = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap();
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

// A nested rewrite is typed per branch, as compilation projects it: `id(z => true)` instantiates
// `id` at `Nat` in the left branch and at `Bool` in the right one.
#[test]
fn a_nested_rewrite_is_typed_in_each_branch() {
    let loaded = load();
    let mut sentence = labelled(&loaded.definition, "TYPED.increment").clone();
    *term_at(&mut sentence, &[0]) = Term::apply(
        "id",
        vec![rewrite(
            Term::apply("z", vec![]),
            Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
        )],
    );
    let typing = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap();

    assert_eq!(
        typing.branches.get(&vec![0]),
        Some(&BranchTyping {
            left: sorted(Some("Nat"), Some("KItem")),
            right: sorted(Some("Bool"), Some("KItem")),
        })
    );
    assert_eq!(
        typing.branches.get(&vec![0, 0]),
        Some(&BranchTyping {
            left: sorted(Some("Nat"), Some("Nat")),
            right: sorted(Some("Bool"), Some("Bool")),
        })
    );
    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(Some("Nat"), Some("Nat")));
    assert_eq!(at(&typing, &[0, 0, 1]), &sorted(Some("Bool"), Some("Bool")));
    let kore = compiled_kore(&relinked(&loaded, "TYPED", "TYPED.increment", sentence)).unwrap();
    assert!(kore.contains("Lblid{SortNat{}}"), "{kore}");
    assert!(kore.contains("Lblid{SortBool{}}"), "{kore}");
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
    let error = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap_err();
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
    let typing = sentence_typing(&loaded.resolved, "TYPED", &sentence).unwrap();

    assert_eq!(at(&typing, &[0, 0, 0]), &sorted(None, Some("Nat")));
    assert_eq!(at(&typing, &[0, 0, 1]), &sorted(None, Some("Nat")));
}

// The free function and a typer built once for the module type every sentence alike, including
// one whose rewrite needs the implicit `KItem` subsorts.
#[test]
fn both_entry_points_agree() {
    let loaded = load();
    let typer = SentenceTyper::new(&loaded.resolved, "TYPED").unwrap();
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
        .definition
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
            sentence_typing(&loaded.resolved, "TYPED", &sentence)
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
    let typer = SentenceTyper::new(&loaded.resolved, module).unwrap();
    let mut checked = 0;
    let sentences = loaded
        .definition
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
        let placements = typing.positions.iter().chain(
            typing
                .branches
                .iter()
                .flat_map(|(path, branches)| [(path, &branches.left), (path, &branches.right)]),
        );
        for (path, position) in placements {
            let (Some(sort), Some(required)) = (&position.sort, &position.required) else {
                continue;
            };
            if sort == required || under_cast(sentence, path) {
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
