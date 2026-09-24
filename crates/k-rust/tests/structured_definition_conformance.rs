use std::collections::BTreeMap;

#[cfg(feature = "z3-inference")]
use k_rust::{
    builtin::embedded,
    outer::{LoadOptions, load_structured},
};
use k_rust::{
    definition::{
        Attributes, Definition, FlatModule, ProductionItem, ResolvedDefinition, Sentence,
    },
    kast::{Label, Sort, Term},
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::parser::parse_definition,
    outer::LoadedDefinition,
};
use serde_json::json;

#[test]
fn reference_bracket_symbol_fixture_matches_k_parsed_json() {
    // reference: kompile test.k --backend haskell --emit-json
    let source = include_str!("fixtures/reference/outer/bracket-symbol/test.k");
    let expected: serde_json::Value = serde_json::from_str(include_str!(
        "fixtures/reference/outer/bracket-symbol/bracket-label.json"
    ))
    .unwrap();
    let parsed = k_rust::outer::parse("bracket-symbol.k", source).unwrap();
    let definition = k_rust::outer::lower(&parsed, "BRACKET-SYMBOL").unwrap();
    let actual = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Production { attributes, .. }
                if attributes.get_str("symbol") == Some("paren") =>
            {
                attributes.get("bracketLabel")
            }
            _ => None,
        })
        .expect("the reference bracket production should be lowered");

    assert_eq!(actual, &expected);
}

#[test]
fn hand_built_definition_conforms_to_the_complete_public_compiler_pipeline() {
    assert_compiles_on_both_backends(structured_definition(false), |artifacts| {
        assert!(artifacts.definition_kore.contains("SortExp"));
        assert_eq!(artifacts.macros_kore, "\n");
    });
}

#[test]
fn structured_configuration_compiles_through_the_public_pipeline() {
    assert_compiles_on_both_backends(structured_definition(true), |artifacts| {
        assert!(
            artifacts.definition_kore.contains("'-LT-'top'-GT-'"),
            "{}",
            artifacts.definition_kore
        );
        assert!(
            artifacts
                .definition_kore
                .contains("LblinitGeneratedTopCell"),
            "{}",
            artifacts.definition_kore
        );
    });
}

#[cfg(feature = "z3-inference")]
#[test]
fn load_structured_compiles_an_authored_instrs_configuration() {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let loaded = load_structured(
            structured_definition_with_configuration_cell("instrs"),
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
                ..LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured loading: {error}"));

        assert!(loaded.definition.modules.iter().all(|module| {
            module.name != "DEFAULT-CONFIGURATION"
                && module
                    .imports
                    .iter()
                    .all(|import| import.name != "DEFAULT-CONFIGURATION")
        }));

        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured input: {error:#?}"));
        assert!(artifacts.definition_kore.contains("instrs"));
        assert!(!artifacts.definition_kore.contains("Lbl'-LT-'k'-GT-'"));
    }
}

#[test]
fn a_labelled_token_production_is_not_a_constructor_and_the_definition_loads() {
    // A `token` production's terms are domain values of its sort, so its symbol must not claim a
    // term-algebra element distinct from them: no `constructor` attribute and no no-confusion
    // axiom, whether or not the sort is hooked.
    for hooked in [false, true] {
        assert_compiles_on_both_backends(labelled_token_definition(hooked), |artifacts| {
            let declaration = artifacts
                .definition_kore
                .lines()
                .find(|line| line.contains("symbol LblstrLit{}()"))
                .unwrap_or_else(|| {
                    panic!("hooked={hooked}: the labelled token symbol is declared")
                });
            assert!(declaration.contains("token{}()"), "{declaration}");
            assert!(!declaration.contains("constructor{}()"), "{declaration}");
            // No-confusion axioms are the `\not` (distinct heads) and `\implies` (injectivity)
            // axioms carrying the `constructor` marker.
            for axiom in artifacts.definition_kore.split("axiom{").skip(1) {
                let no_confusion = axiom.contains("constructor{}()")
                    && (axiom.contains("\\not{") || axiom.contains("\\implies{"));
                assert!(
                    !(no_confusion && (axiom.contains("LblstrLit") || axiom.contains("LblidLit"))),
                    "hooked={hooked}: a no-confusion axiom mentions a token symbol: axiom{{{axiom}"
                );
            }
            let parsed = parse_definition(&artifacts.definition_kore).unwrap();
            k_rust_backend::definition::BackendDefinition::internalize(&parsed, "MAIN")
                .unwrap_or_else(|error| panic!("hooked={hooked}: backend load failed: {error}"));
        });
    }
}

fn labelled_token_definition(hooked: bool) -> Definition {
    let mut local_sentences = Vec::new();
    if hooked {
        local_sentences.push(Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Str"),
            attributes: Attributes::new(BTreeMap::from([("hook".into(), json!("STRING.String"))])),
        });
    }
    // Two labelled token productions on one sort: were they constructors, their pair would get a
    // no-confusion axiom.
    for (label, regex) in [("strLit", "[a-z]+"), ("idLit", "[A-Z]+")] {
        local_sentences.push(Sentence::Production {
            label: Some(Label::new(label)),
            parameters: Vec::new(),
            sort: Sort::new("Str"),
            items: vec![ProductionItem::regex(regex)],
            attributes: Attributes::new(BTreeMap::from([("token".into(), json!(""))])),
        });
    }
    local_sentences.push(Sentence::Production {
        label: Some(Label::new("wrap")),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![
            ProductionItem::Terminal("wrap(".into()),
            ProductionItem::NonTerminal {
                sort: Sort::new("Str"),
                name: None,
            },
            ProductionItem::Terminal(")".into()),
        ],
        attributes: Attributes::default(),
    });
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: local_sentences
                .into_iter()
                .map(std::sync::Arc::new)
                .collect(),
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

/// A bracket's `label` names its syntax-module symbol and the tag its priority and associativity groups use, so a structured bracket labelled `paren` without a `symbol` attribute is declared with the relations that name `paren`, as the source form `[bracket, symbol(paren)]` is.
#[cfg(feature = "z3-inference")]
#[test]
fn structured_labelled_bracket_declares_its_syntax_relations() {
    let mut definition = structured_definition(false);
    let exp = || ProductionItem::NonTerminal {
        sort: Sort::new("Exp"),
        name: None,
    };
    let sentences = &mut definition.modules[0].local_sentences;
    sentences.push(std::sync::Arc::new(Sentence::Production {
        label: Some(Label::new("paren")),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![
            ProductionItem::Terminal("(".into()),
            exp(),
            ProductionItem::Terminal(")".into()),
        ],
        attributes: Attributes::new(BTreeMap::from([
            ("bracket".into(), json!("")),
            ("format".into(), json!("%1 %2 %3")),
        ])),
    }));
    sentences.push(std::sync::Arc::new(Sentence::Production {
        label: Some(Label::new("plus")),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![exp(), ProductionItem::Terminal("+".into()), exp()],
        attributes: Attributes::default(),
    }));
    sentences.push(std::sync::Arc::new(Sentence::SyntaxPriority {
        priorities: vec![vec!["paren".into()], vec!["plus".into()]],
        attributes: Attributes::default(),
    }));

    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let loaded = load_structured(
            definition.clone(),
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![backend.excluded_module_attribute().into()],
                ..LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured loading: {error}"));
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured input: {error:#?}"));

        let syntax = &artifacts.syntax_definition_kore;
        let declaration = syntax
            .find("symbol Lblparen{}(")
            .map(|start| {
                let rest = &syntax[start..];
                &rest[..rest
                    .find("\n  ]")
                    .expect("the declaration's attributes close")]
            })
            .unwrap_or_else(|| {
                panic!(
                    "{backend}: `paren` is not declared in the syntax module:\n{}",
                    syntax
                )
            });
        for attribute in ["bracket{}()", "format{}(", "left{}(", "right{}("] {
            assert!(
                declaration.contains(attribute),
                "{backend}: missing `{attribute}` in {declaration}"
            );
        }
        assert!(
            declaration.contains("priorities{}(Lblplus{}())"),
            "{backend}: `paren` does not carry its priority over `plus`: {declaration}"
        );
    }
}

fn assert_compiles_on_both_backends(
    definition: Definition,
    assert_artifacts: impl Fn(&k_rust::kompile::CompiledKoreArtifacts),
) {
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let loaded = LoadedDefinition {
        files: Vec::new(),
        source_table: Default::default(),
        definition,
        resolved,
        diagnostics: Vec::new(),
    };

    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let artifacts = compile_loaded_definition(
            &loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected structured input: {error:#?}"));

        assert!(parse_definition(&artifacts.definition_kore).is_ok());
        assert!(parse_definition(&artifacts.syntax_definition_kore).is_ok());
        assert_artifacts(&artifacts);
    }
}

fn structured_definition(with_configuration: bool) -> Definition {
    structured_definition_with_optional_configuration_cell(
        with_configuration.then_some("top"),
        with_configuration,
    )
}

#[cfg(feature = "z3-inference")]
fn structured_definition_with_configuration_cell(cell: &str) -> Definition {
    structured_definition_with_optional_configuration_cell(Some(cell), false)
}

fn structured_definition_with_optional_configuration_cell(
    configuration_cell: Option<&str>,
    declare_map_lookup: bool,
) -> Definition {
    let mut local_sentences = vec![
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Int"),
            items: vec![ProductionItem::regex("[0-9]+")],
            attributes: Attributes::new(BTreeMap::from([("token".into(), json!(""))])),
        },
        Sentence::Production {
            label: None,
            parameters: Vec::new(),
            sort: Sort::new("Exp"),
            items: vec![ProductionItem::NonTerminal {
                sort: Sort::new("Int"),
                name: None,
            }],
            attributes: Attributes::default(),
        },
    ];
    if declare_map_lookup {
        // Configuration initializers read their variables from the configuration map. Structured
        // callers currently supply that builtin closure themselves; this minimal declaration is
        // the only prelude contract this fixture needs.
        local_sentences.push(Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Map"),
            attributes: Attributes::default(),
        });
        local_sentences.push(Sentence::Production {
            label: Some(Label::new("Map:lookup")),
            parameters: Vec::new(),
            sort: Sort::new("KItem"),
            items: vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new("Map"),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: Sort::new("KItem"),
                    name: None,
                },
            ],
            attributes: Attributes::new(BTreeMap::from([("function".into(), json!(""))])),
        });
    }
    if let Some(configuration_cell) = configuration_cell {
        local_sentences.push(Sentence::Configuration {
            body: config_cell(
                configuration_cell,
                Term::apply(
                    "#SemanticCastToExp",
                    vec![Term::Token {
                        token: "$PGM".into(),
                        sort: Sort::new("KConfigVar"),
                    }],
                ),
            ),
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes: Attributes::default(),
        });
    }

    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: local_sentences
                .into_iter()
                .map(std::sync::Arc::new)
                .collect(),
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

fn config_cell(name: &str, contents: Term) -> Term {
    let cell_name = || Term::Token {
        token: name.into(),
        sort: Sort::new("#CellName"),
    };
    Term::apply(
        "#configCell",
        vec![
            cell_name(),
            Term::apply("#cellPropertyListTerminator", vec![]),
            contents,
            cell_name(),
        ],
    )
}

// A bracket production only groups program text: the parsers erase it before a term exists, so
// its label names the syntax-module symbol and the priority tag, never a semantic symbol.

#[cfg(feature = "z3-inference")]
#[test]
fn structured_labelled_bracket_is_declared_only_in_the_syntax_module() {
    let loaded = load_structured(
        labelled_bracket_structured_definition(),
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("load_structured rejected the definition: {error}"));
    assert_labelled_bracket_is_syntax_only(&loaded);
}

#[test]
fn source_labelled_bracket_is_declared_only_in_the_syntax_module() {
    assert_labelled_bracket_is_syntax_only(&loaded_source(LABELLED_BRACKET_SOURCE));
}

#[test]
fn labelled_bracket_stays_out_of_the_backend_constructor_domain() {
    use k_rust_backend::{
        definition::BackendDefinition,
        rule::Predicate,
        simplify::{SimplificationOptions, simplify_predicates_with_solver},
        smt::NoSolver,
        term::{Sort as BackendSort, Term as BackendTerm, Variable},
    };

    let artifacts = compile_loaded_definition(
        &loaded_source(LABELLED_BRACKET_SOURCE),
        CompileOptions::default(),
    )
    .expect("the definition should compile");
    // The named field generates no projection through the bracket either.
    assert!(
        !artifacts.definition_kore.contains("Lblshade"),
        "definition.kore mentions the bracket symbol:\n{}",
        artifacts.definition_kore
    );
    let syntax = parse_definition(&artifacts.definition_kore).expect("definition.kore parses");
    let definition =
        BackendDefinition::internalize(&syntax, "MAIN").expect("definition.kore internalizes");
    let color = BackendTerm::variable(Variable::new("X", BackendSort::simple("SortColor")));
    let excluded = |name: &str| {
        let constructor = definition
            .internalize_term(
                &k_rust::kore::parser::parse_pattern(&format!("Lbl{name}{{}}()")).unwrap(),
                &[],
            )
            .unwrap();
        Predicate::Not(Box::new(Predicate::Equals(color.clone(), constructor)))
    };

    // `red` and `blue` are every term of `Color`; the bracket `shade` adds none.
    let simplified = simplify_predicates_with_solver(
        &definition,
        &[excluded("red"), excluded("blue")],
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("the exclusions should simplify");
    assert_eq!(simplified, vec![Predicate::False]);
    let simplified = simplify_predicates_with_solver(
        &definition,
        &[excluded("red")],
        &[],
        SimplificationOptions::default(),
        &NoSolver,
    )
    .expect("the exclusion should simplify");
    assert_ne!(simplified, vec![Predicate::False]);
}

const LABELLED_BRACKET_SOURCE: &str = r#"
module MAIN
  syntax Int ::= r"[0-9]+" [token]
  syntax Exp ::= Int
               | "(" Exp ")" [bracket, symbol(paren)]
               > Exp "*" Exp [symbol(mul), left]
               > Exp "+" Exp [symbol(plus), left]
  syntax Color ::= "red" [symbol(red)]
                 | "blue" [symbol(blue)]
                 | "[" inner: Color "]" [bracket, symbol(shade)]
endmodule
"#;

fn loaded_source(source: &str) -> LoadedDefinition {
    let parsed = k_rust::outer::parse("labelled-bracket.k", source).expect("source parses");
    let definition = k_rust::outer::lower(&parsed, "MAIN").expect("source lowers");
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    LoadedDefinition {
        files: Vec::new(),
        source_table: Default::default(),
        definition,
        resolved,
        diagnostics: Vec::new(),
    }
}

/// The production shape a structured client sends for a bracket: a label plus `bracket`.
#[cfg(feature = "z3-inference")]
fn labelled_bracket_structured_definition() -> Definition {
    let production = |label: Option<&str>, sort: &str, items, attributes: &[(&str, &str)]| {
        std::sync::Arc::new(Sentence::Production {
            label: label.map(Label::new),
            parameters: Vec::new(),
            sort: Sort::new(sort),
            items,
            attributes: Attributes::new(
                attributes
                    .iter()
                    .map(|(key, value)| ((*key).to_owned(), json!(value)))
                    .collect(),
            ),
        })
    };
    let exp = || ProductionItem::NonTerminal {
        sort: Sort::new("Exp"),
        name: None,
    };
    let terminal = |text: &str| ProductionItem::Terminal(text.into());
    Definition {
        main_module: "MAIN".into(),
        modules: vec![FlatModule {
            name: "MAIN".into(),
            imports: Vec::new(),
            local_sentences: vec![
                production(
                    None,
                    "Int",
                    vec![ProductionItem::regex("[0-9]+")],
                    &[("token", "")],
                ),
                production(
                    None,
                    "Exp",
                    vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Int"),
                        name: None,
                    }],
                    &[],
                ),
                production(
                    Some("paren"),
                    "Exp",
                    vec![terminal("("), exp(), terminal(")")],
                    &[("bracket", ""), ("format", "%1%2%3")],
                ),
                production(
                    Some("plus"),
                    "Exp",
                    vec![exp(), terminal("+"), exp()],
                    &[("left", "")],
                ),
                production(
                    Some("mul"),
                    "Exp",
                    vec![exp(), terminal("*"), exp()],
                    &[("left", "")],
                ),
                std::sync::Arc::new(Sentence::SyntaxPriority {
                    priorities: vec![vec!["mul".into()], vec!["plus".into()]],
                    attributes: Attributes::default(),
                }),
            ],
            attributes: Attributes::default(),
        }],
        attributes: Attributes::default(),
    }
}

fn assert_labelled_bracket_is_syntax_only(loaded: &LoadedDefinition) {
    for backend in [CompilationBackend::Rust, CompilationBackend::Llvm] {
        let artifacts = compile_loaded_definition(
            loaded,
            CompileOptions {
                backend,
                ..CompileOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend} rejected the definition: {error:#?}"));

        // No declaration and no axiom of the semantic module mentions the bracket.
        assert!(
            !artifacts.definition_kore.contains("Lblparen"),
            "{backend}: definition.kore mentions the bracket symbol:\n{}",
            artifacts.definition_kore
        );
        assert!(
            artifacts.definition_kore.contains("symbol Lblmul{}"),
            "{backend}: definition.kore lost a real constructor"
        );

        let syntax = parse_definition(&artifacts.syntax_definition_kore)
            .expect("syntaxDefinition.kore parses");
        let declarations = syntax
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .filter_map(|sentence| match sentence {
                k_rust::kore::ast::Sentence::SymbolDeclaration {
                    symbol, attributes, ..
                } if symbol.name == "Lblparen" => Some(attributes),
                _ => None,
            })
            .collect::<Vec<_>>();
        let [attributes] = declarations.as_slice() else {
            panic!("{backend}: syntaxDefinition.kore declares the bracket {declarations:?}");
        };
        let names = attributes
            .0
            .iter()
            .filter_map(|attribute| match attribute {
                k_rust::kore::ast::Pattern::Application { symbol, .. } => {
                    Some(symbol.name.as_str())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        for retained in ["bracket", "format", "terminals"] {
            assert!(
                names.contains(&retained),
                "{backend}: the syntax-module bracket lost `{retained}`: {names:?}"
            );
        }
    }

    let token = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    };
    let parsed = k_rust::inner::ProgramParser::new(&loaded.definition, "MAIN")
        .expect("program parser")
        .parse(&Sort::new("Exp"), "(1 + 2) * 3")
        .expect("the program parses");
    assert_eq!(
        parsed,
        Term::apply(
            "mul",
            vec![
                Term::apply("plus", vec![token("1"), token("2")]),
                token("3")
            ]
        )
    );
}
