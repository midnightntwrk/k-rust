use k_rust::{
    builtin,
    definition::{AttributeKey, Definition, PartialOrder, ResolvedDefinition, Sentence},
    kast::{Sort, Term},
    kompile::{
        CompilationBackend, CompileOptions, compile_loaded_definition,
        resolve_semantic_casts_in_sentence,
    },
    outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation, load_structured},
};

const COUNTER: &str = include_str!("fixtures/semantic_cast_sorts/counter.k");
const PRELUDE: &str = include_str!("fixtures/semantic_cast_sorts/portable-prelude.k");

fn options(backend: CompilationBackend) -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![
            builtin::embedded("kast.md").unwrap(),
            ResolvedSource::new("portable-prelude.k", PRELUDE),
        ],
        excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
        ..LoadOptions::default()
    }
}

fn load(backend: CompilationBackend) -> LoadedDefinition {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    load_for_compilation(
        ResolvedSource::new("counter.k", COUNTER),
        "COUNTER",
        None,
        &mut resolver,
        &options(backend),
    )
    .unwrap()
    .0
}

fn labelled<'a>(definition: &'a mut Definition, label: &str) -> &'a mut Sentence {
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "COUNTER")
        .unwrap();
    let sentence = module
        .local_sentences
        .iter_mut()
        .find(|sentence| sentence.attributes().string(AttributeKey::Label) == Some(label))
        .unwrap();
    k_rust::definition::sentence_mut(sentence)
}

fn variable(name: &str, sort: Option<&str>) -> Term {
    Term::Variable {
        name: name.into(),
        sort: sort.map(Sort::new),
    }
}

fn cast(sort: &str, argument: Term) -> Term {
    Term::apply(format!("#SemanticCastTo{sort}"), vec![argument])
}

fn app(label: &str, arguments: Vec<Term>) -> Term {
    Term::apply(label, arguments)
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn fallback(definition: &mut Definition, body: Term) {
    let Sentence::Rule { body: slot, .. } = labelled(definition, "COUNTER.fallback") else {
        unreachable!()
    };
    *slot = body;
}

fn relink(base: &LoadedDefinition, definition: Definition) -> LoadedDefinition {
    base.with_definition(definition).unwrap()
}

fn subsorts(resolved: &ResolvedDefinition, module: &str) -> k_rust::definition::PartialOrder<Sort> {
    resolved
        .subsorts(resolved.module_id(module).unwrap())
        .unwrap()
}

fn compile(
    loaded: &LoadedDefinition,
    backend: CompilationBackend,
) -> Result<k_rust::kompile::CompiledKoreArtifacts, k_rust::kompile::CompileError> {
    compile_loaded_definition(
        loaded,
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
}

fn structured(backend: CompilationBackend, sentence: Sentence) -> LoadedDefinition {
    let parsed = k_rust::outer::parse("counter.k", COUNTER).unwrap();
    let mut definition = k_rust::outer::lower(&parsed, "COUNTER").unwrap();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "COUNTER")
        .unwrap();
    let slot = module
        .local_sentences
        .iter_mut()
        .rev()
        .find(|sentence| {
            matches!(&***sentence, Sentence::Bubble { contents, .. } if contents.contains("choose(B) => selected(B)"))
        })
        .unwrap();
    *k_rust::definition::sentence_mut(slot) = sentence;
    load_structured(definition, &options(backend)).unwrap()
}

#[test]
fn conflicting_variable_casts_fail_on_relink_and_structured_paths() {
    let cases = [
        (
            "top-level",
            rewrite(
                cast("Bool", variable("B", None)),
                cast("Nat", variable("B", None)),
            ),
            "incomparable cast bounds Bool and Nat",
        ),
        (
            "nested",
            rewrite(
                app("choose", vec![cast("Bool", variable("B", None))]),
                app("selected", vec![cast("Nat", variable("B", None))]),
            ),
            "incomparable cast bounds Bool and Nat",
        ),
        (
            "own-sort-outside-cast",
            rewrite(
                cast("Nat", variable("X", Some("Bool"))),
                cast("Nat", variable("X", Some("Bool"))),
            ),
            "explicit sort Bool outside semantic cast sort Nat",
        ),
    ];
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let base = load(backend);
        for (name, body, expected) in &cases {
            let mut definition = base.definition().clone();
            fallback(&mut definition, body.clone());
            let sentence = labelled(&mut definition, "COUNTER.fallback").clone();
            for (path, loaded) in [
                ("relink", relink(&base, definition)),
                ("structured", structured(backend, sentence)),
            ] {
                let error = compile(&loaded, backend).unwrap_err();
                assert_eq!(
                    error.stage, "resolve semantic casts",
                    "{backend} {name} {path}: {error:?}"
                );
                assert!(error.message.contains("COUNTER.fallback"), "{error:?}");
                assert!(error.message.contains("variable"), "{error:?}");
                assert!(
                    error.message.contains(expected),
                    "{backend} {name} {path}: {error:?}"
                );
            }
        }
    }
}

#[test]
fn sortless_variable_at_different_position_sorts_reports_both_causes() {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let base = load(backend);
        let mut definition = base.definition().clone();
        fallback(
            &mut definition,
            rewrite(
                app("counter", vec![variable("X", None), app("z", vec![])]),
                app("choose", vec![variable("X", None)]),
            ),
        );
        let error = compile(&relink(&base, definition), backend).unwrap_err();
        assert_eq!(error.stage, "emit KORE", "{backend}: {error:?}");
        assert!(
            error.message.contains("variable VarX"),
            "{backend}: {error:?}"
        );
        assert!(error.message.contains("SortNat{}"), "{backend}: {error:?}");
        assert!(error.message.contains("SortBool{}"), "{backend}: {error:?}");
        assert!(
            error.message.contains("COUNTER.fallback"),
            "{backend}: {error:?}"
        );
        assert!(
            error
                .message
                .contains("authored sortless variable used at positions of different sorts"),
            "{backend}: {error:?}"
        );
        assert!(
            error
                .message
                .contains("kompile pass reusing a variable name"),
            "{backend}: {error:?}"
        );
    }
}

#[test]
fn consistent_annotations_and_bare_occurrences_compile() {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let base = load(backend);
        compile(&base, backend).unwrap();
        for sort in [None, Some("Nat")] {
            let mut definition = base.definition().clone();
            fallback(
                &mut definition,
                rewrite(
                    app(
                        "counter",
                        vec![cast("Nat", variable("X", sort)), app("z", vec![])],
                    ),
                    app("counter", vec![variable("X", None), app("z", vec![])]),
                ),
            );
            let sentence = labelled(&mut definition, "COUNTER.fallback").clone();
            compile(&relink(&base, definition), backend).unwrap();
            compile(&structured(backend, sentence), backend).unwrap();
        }
        let mut definition = base.definition().clone();
        fallback(
            &mut definition,
            rewrite(
                app(
                    "counter",
                    vec![cast("Nat", variable("X", None)), app("z", vec![])],
                ),
                app(
                    "counter",
                    vec![cast("K", variable("X", None)), app("z", vec![])],
                ),
            ),
        );
        let sentence = labelled(&mut definition, "COUNTER.fallback").clone();
        compile(&relink(&base, definition), backend).unwrap();
        compile(&structured(backend, sentence), backend).unwrap();
    }
}

#[test]
fn standalone_resolution_treats_anonymous_occurrences_independently() {
    let base = load(CompilationBackend::Rust);
    let sentence = Sentence::Rule {
        body: rewrite(
            cast("Bool", variable("_", None)),
            cast("Nat", variable("_", None)),
        ),
        requires: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        ensures: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        attributes: Default::default(),
    };
    resolve_semantic_casts_in_sentence(&subsorts(base.resolved(), "COUNTER"), sentence).unwrap();
}

#[test]
fn standalone_resolution_checks_body_and_conditions_together() {
    let base = load(CompilationBackend::Rust);
    let sentence = Sentence::Rule {
        body: cast("Bool", variable("B", None)),
        requires: cast("Nat", variable("B", None)),
        ensures: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        attributes: Default::default(),
    };
    let error = resolve_semantic_casts_in_sentence(&subsorts(base.resolved(), "COUNTER"), sentence)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("variable B has incomparable cast bounds Bool and Nat")
    );
}

#[test]
fn an_explicit_variable_sort_may_be_below_its_cast_bound() {
    let source = r#"
module SORTS
  syntax Small ::= "s" [symbol(s)]
  syntax Large ::= Small
endmodule
"#;
    let parsed = k_rust::outer::parse("sorts.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "SORTS").unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let sentence = Sentence::Rule {
        body: rewrite(
            cast("Large", variable("X", Some("Small"))),
            variable("X", None),
        ),
        requires: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        ensures: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        attributes: Default::default(),
    };
    let resolved_sentence =
        resolve_semantic_casts_in_sentence(&subsorts(&resolved, "SORTS"), sentence).unwrap();
    let Sentence::Rule { body, .. } = resolved_sentence else {
        unreachable!()
    };
    let Term::Rewrite { left, right } = body.unannotated() else {
        unreachable!()
    };
    assert!(
        matches!(left.unannotated(), Term::Variable { sort: Some(sort), .. } if sort == &Sort::new("Small"))
    );
    assert!(
        matches!(right.unannotated(), Term::Variable { sort: Some(sort), .. } if sort == &Sort::new("Small"))
    );
}

#[test]
fn the_least_comparable_cast_bound_types_every_occurrence() {
    let source = r#"
module SORTS
  syntax Small ::= "s" [symbol(s)]
  syntax Large ::= Small
endmodule
"#;
    let parsed = k_rust::outer::parse("sorts.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "SORTS").unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let sentence = Sentence::Rule {
        body: rewrite(
            cast("Large", variable("X", None)),
            cast("Small", variable("X", None)),
        ),
        requires: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        ensures: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        attributes: Default::default(),
    };
    let resolved_sentence =
        resolve_semantic_casts_in_sentence(&subsorts(&resolved, "SORTS"), sentence).unwrap();
    let Sentence::Rule { body, .. } = resolved_sentence else {
        unreachable!()
    };
    let Term::Rewrite { left, right } = body.unannotated() else {
        unreachable!()
    };
    assert!(
        matches!(left.unannotated(), Term::Variable { sort: Some(sort), .. } if sort == &Sort::new("Small"))
    );
    assert!(
        matches!(right.unannotated(), Term::Variable { sort: Some(sort), .. } if sort == &Sort::new("Small"))
    );
}

#[test]
fn exists_binder_uses_the_bound_occurrences_narrower_sort() {
    let base = load(CompilationBackend::Rust);
    let sentence = Sentence::Rule {
        body: app(
            "#Exists",
            vec![
                cast("K", variable("_Gen0", None)),
                app("choose", vec![cast("Bool", variable("_Gen0", None))]),
            ],
        ),
        requires: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        ensures: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        attributes: Default::default(),
    };
    let resolved =
        resolve_semantic_casts_in_sentence(&subsorts(base.resolved(), "COUNTER"), sentence)
            .unwrap();
    let Sentence::Rule { body, .. } = resolved else {
        unreachable!()
    };
    let mut sorts = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, sort } = term.unannotated()
            && name == "_Gen0"
        {
            sorts.push(sort.clone());
        }
    });
    assert_eq!(sorts, vec![Some(Sort::new("Bool")); 2]);
}

#[test]
fn parser_subsort_reaches_kitem_through_a_user_sort() {
    let order = PartialOrder::new([(Sort::new("#P"), Sort::new("U"))]).unwrap();
    let sentence = Sentence::Rule {
        body: cast("#P", variable("X", None)),
        requires: cast("KItem", variable("X", None)),
        ensures: cast("U", variable("X", None)),
        attributes: Default::default(),
    };
    let resolved = resolve_semantic_casts_in_sentence(&order, sentence).unwrap();
    let mut sorts = Vec::new();
    if let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = resolved
    {
        for root in [&body, &requires, &ensures] {
            root.visit_preorder(&mut |term| {
                if let Term::Variable { name, sort } = term.unannotated()
                    && name == "X"
                {
                    sorts.push(sort.clone());
                }
            });
        }
    } else {
        unreachable!();
    }
    assert_eq!(sorts, vec![Some(Sort::new("#P")); 3]);
}

#[test]
fn reports_each_independent_variable_conflict() {
    let order = PartialOrder::new([]).unwrap();
    let sentence = Sentence::Rule {
        body: rewrite(
            cast("Bool", variable("B", None)),
            cast("Nat", variable("B", None)),
        ),
        requires: rewrite(
            cast("Bool", variable("C", None)),
            cast("Nat", variable("C", None)),
        ),
        ensures: Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        },
        attributes: Default::default(),
    };
    let error = resolve_semantic_casts_in_sentence(&order, sentence).unwrap_err();
    assert_eq!(error.diagnostics.len(), 2);
    assert!(error.diagnostics[0].message.contains("variable B"));
    assert!(error.diagnostics[1].message.contains("variable C"));
    assert!(error.diagnostics.iter().all(|diagnostic| {
        diagnostic.message.contains("sentence <unlabelled>")
            && diagnostic
                .message
                .contains("incomparable cast bounds Bool and Nat")
    }));
}

const EXPS: &str = include_str!("fixtures/semantic_cast_sorts/exps.k");

/// `exps.k` loaded for the Rust backend; its rule `EXPS.cast` is the parsed `plus((E => z):Nat, z)`.
fn load_exps() -> LoadedDefinition {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    load_for_compilation(
        ResolvedSource::new("exps.k", EXPS),
        "EXPS",
        None,
        &mut resolver,
        &options(CompilationBackend::Rust),
    )
    .unwrap()
    .0
}

/// The rule `EXPS.cast` of `base` with `body`, reached through both loader routes that take terms
/// rather than text: a loaded definition edited and relinked, and a structured definition.
fn exps_with_cast_body(
    base: &LoadedDefinition,
    body: Term,
) -> [(&'static str, LoadedDefinition); 2] {
    let mut definition = base.definition().clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "EXPS")
        .unwrap();
    let slot = module
        .local_sentences
        .iter_mut()
        .find(|sentence| sentence.attributes().string(AttributeKey::Label) == Some("EXPS.cast"))
        .unwrap();
    let Sentence::Rule { body: old, .. } = k_rust::definition::sentence_mut(slot) else {
        unreachable!()
    };
    *old = body;
    let sentence = (**slot).clone();
    let parsed = k_rust::outer::parse("exps.k", EXPS).unwrap();
    let mut structured = k_rust::outer::lower(&parsed, "EXPS").unwrap();
    let module = structured
        .modules
        .iter_mut()
        .find(|module| module.name == "EXPS")
        .unwrap();
    let bubble = module
        .local_sentences
        .iter_mut()
        .find(|sentence| {
            matches!(&***sentence, Sentence::Bubble { contents, .. } if contents.contains("(E => z):Nat"))
        })
        .unwrap();
    *k_rust::definition::sentence_mut(bubble) = sentence;
    [
        ("relink", relink(base, definition)),
        (
            "structured",
            load_structured(structured, &options(CompilationBackend::Rust)).unwrap(),
        ),
    ]
}

/// The pattern of the axiom labelled `label` in `kore`, without its attributes (which hold a
/// hash of the sentence) and without whitespace.
fn axiom_pattern(kore: &str, label: &str) -> String {
    let end = kore
        .find(&format!("label{{}}(\"{label}\")"))
        .unwrap_or_else(|| panic!("no axiom labelled {label}"));
    let start = kore[..end].rfind("axiom{").unwrap();
    let attributes = kore[..end].rfind('[').unwrap();
    kore[start..attributes].split_whitespace().collect()
}

fn compiled_cast_axiom(loaded: &LoadedDefinition) -> Result<String, k_rust::kompile::CompileError> {
    compile(loaded, CompilationBackend::Rust)
        .map(|artifacts| axiom_pattern(&artifacts.definition_kore, "EXPS.cast"))
}

fn z() -> Term {
    app("z", vec![])
}

// A cast is a sort membership constraint on the value of its operand, and the value of a cast is
// the value of its operand: `t:T:S` claims that `t` is in both `T` and `S`. The static sort of
// `t:T` is `T`, so an enclosing cast incomparable with `T` claims what no term can satisfy.
#[test]
fn a_nested_cast_constrains_its_operand_by_both_sorts() {
    let base = load_exps();
    // A variable under `Nat` and `Exp` is a `Nat`, wherever the outer cast is.
    let variable_body = app(
        "plus",
        vec![
            cast("Nat", cast("Exp", variable("X", None))),
            rewrite(z(), variable("X", None)),
        ],
    );
    // A function result of sort `Exp` claimed to be a `Nat` is projected to `Nat`; the `Exp`
    // cast around that claim is an upcast and does not undo it.
    let term_body = app(
        "plus",
        vec![
            variable("Y", Some("Exp")),
            rewrite(z(), cast("Exp", cast("Nat", app("f", vec![z()])))),
        ],
    );
    let mut failures = Vec::new();
    for (route, loaded) in exps_with_cast_body(&base, variable_body) {
        let axiom = compiled_cast_axiom(&loaded).unwrap();
        if !axiom.contains("inj{SortNat{},SortExp{}}(VarX:SortNat{})")
            || axiom.contains("VarX:SortExp{}")
        {
            failures.push(format!("variable, {route}: {axiom}"));
        }
    }
    for (route, loaded) in exps_with_cast_body(&base, term_body) {
        let axiom = compiled_cast_axiom(&loaded).unwrap();
        if !axiom.contains("inj{SortNat{},SortExp{}}(Lblproject'Coln'Nat{}(") {
            failures.push(format!("function result, {route}: {axiom}"));
        }
    }
    // `z:Bool` claims a `Nat` constructor is a `Bool`, whatever cast encloses the claim.
    let incomparable = app(
        "plus",
        vec![
            variable("Y", Some("Exp")),
            rewrite(z(), cast("Exp", cast("Bool", z()))),
        ],
    );
    for (route, loaded) in exps_with_cast_body(&base, incomparable) {
        match compiled_cast_axiom(&loaded) {
            Err(error)
                if error.stage == "resolve semantic casts"
                    && error.message.contains(
                        "semantic cast sort Exp is incomparable with the nested cast sort Bool",
                    ) => {}
            other => failures.push(format!("incomparable, {route}: {other:?}")),
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}

// A rewrite `C[L => R]` denotes `C[L]` on the left of the rule and `C[R]` on the right, so a cast
// around it, `C[(L => R):S]`, constrains each side as a cast written on that side would:
// `C[L:S] => C[R:S]`. The parser writes the left side's cast itself (`(E => z):Nat` loads as
// `#SemanticCastToNat(#SemanticCastToNat(E) => z)`); a term without it means the same.
#[test]
fn a_cast_around_a_rewrite_constrains_each_side() {
    let base = load_exps();
    let parsed = compiled_cast_axiom(&base).unwrap();
    assert!(
        parsed.contains("Lblplus{}(inj{SortNat{},SortExp{}}(VarE:SortNat{})"),
        "{parsed}"
    );
    let cast_rewrite =
        |left: Term, right: Term| app("plus", vec![cast("Nat", rewrite(left, right)), z()]);
    let mut failures = Vec::new();
    for (route, loaded) in exps_with_cast_body(&base, cast_rewrite(variable("E", None), z())) {
        let axiom = compiled_cast_axiom(&loaded).unwrap();
        if axiom != parsed {
            failures.push(format!("unsorted side, {route}: {axiom}"));
        }
    }
    // The bound types every occurrence of the variable.
    let shared = app(
        "plus",
        vec![
            cast("Nat", rewrite(variable("E", None), z())),
            variable("E", None),
        ],
    );
    for (route, loaded) in exps_with_cast_body(&base, shared) {
        let axiom = compiled_cast_axiom(&loaded).unwrap();
        if !axiom.contains("inj{SortNat{},SortExp{}}(VarE:SortNat{})")
            || axiom.contains("VarE:SortExp{}")
        {
            failures.push(format!("shared variable, {route}: {axiom}"));
        }
    }
    for (route, loaded) in exps_with_cast_body(&base, cast_rewrite(variable("E", Some("Exp")), z()))
    {
        match compiled_cast_axiom(&loaded) {
            Err(error)
                if error.stage == "resolve semantic casts"
                    && error.message.contains(
                        "variable E has explicit sort Exp outside semantic cast sort Nat",
                    ) => {}
            other => failures.push(format!("sorted side, {route}: {other:?}")),
        }
    }
    // A right side of sort `Exp` claimed to be a `Nat` is projected, as under a direct cast.
    for (route, loaded) in exps_with_cast_body(
        &base,
        cast_rewrite(variable("E", None), app("f", vec![variable("E", None)])),
    ) {
        let axiom = compiled_cast_axiom(&loaded).unwrap();
        if !axiom.contains("inj{SortNat{},SortExp{}}(Lblproject'Coln'Nat{}(") {
            failures.push(format!("function side, {route}: {axiom}"));
        }
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
