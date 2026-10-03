// The embedded standard prelude loads in the portable build to the same definition as in the
// z3-inference build (inner_rules::the_standard_prelude_loads_to_the_same_definition_in_both_builds).
// Fixtures gated on `z3-inference` below are gated for their own rules or pinned results, not for
// the prelude: parametric sort inference, an ambiguous forest outside the portable decision, or
// an assertion not yet checked against the portable build.

use indoc::indoc;
use k_rust::definition::ResolvedDefinition;
use k_rust::kast::convert::{Converter, convert, convert_sort};
use k_rust::kompile::{
    TermConverter, declaration_modules, declaration_modules_from_resolved_with_options,
    encode_kore_label, encode_kore_sort, module_to_kore,
};
use k_rust::kore::ast::{Pattern, Sentence};
use k_rust::kore::parser::{parse_definition, parse_module, parse_sentence};
use k_rust::kore::printer::Printer;
#[cfg(feature = "z3-inference")]
use k_rust::{
    builtin::embedded,
    definition::CheckMode,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, ResolvedSource, load_with_options},
};
use k_rust::{kast, kast::Label, outer};
use serde::Deserialize;
use serde_json::json;

fn lowered(source: &str, main_module: &str) -> k_rust::definition::Definition {
    let parsed = outer::parse("declarations.k", source).expect("definition should parse");
    outer::lower(&parsed, main_module).expect("definition should lower")
}

fn rules(source: &str, main_module: &str) -> k_rust::definition::Definition {
    let definition = k_rust::inner::resolve_rule_bubbles(&lowered(source, main_module))
        .expect("rule bubbles should resolve");
    k_rust::kompile::resolve_semantic_casts(&definition)
        .expect("semantic casts should lower to sort metadata before KORE emission")
}

#[test]
fn a_production_with_sort_parameters_has_no_subsort_axiom() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "g"
          syntax {S} KItem ::= S
        endmodule
    "#};
    let definition = k_rust::kompile::subsort_kitem(&rules(source, "MAIN"))
        .expect("the per-sort KItem subsorts should generate");
    let modules = module_to_kore(&definition, "MAIN").expect("KORE modules should emit");
    let printer = Printer::pretty(100);
    for module in [&modules.semantics, &modules.syntax] {
        let kore = printer.print_module(module);
        assert!(!kore.contains("subsort{SortS"), "{kore}");
        assert!(!kore.contains("SortS}"), "{kore}");
        assert!(kore.contains("subsort{SortFoo{}, SortKItem{}}"), "{kore}");
    }
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct StrictnessAttributeOracle {
    heat_labels: Vec<String>,
    cool_labels: Vec<String>,
    heat_attributes: Vec<String>,
    cool_attributes: Vec<String>,
}

#[cfg(feature = "z3-inference")]
#[test]
fn strictness_rules_do_not_emit_frontend_only_production_attributes() {
    // reference: k/result/bin/kompile --backend haskell --main-module ASSOC-STRICT test.k
    let source = include_str!("fixtures/reference/kompile/assoc-strict/test.k");
    let oracle: StrictnessAttributeOracle = toml::from_str(include_str!(
        "fixtures/reference/kompile/assoc-strict/attributes.toml"
    ))
    .expect("reference attribute oracle should parse");
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("assoc-strict.k", source),
        "ASSOC-STRICT",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("reference fixture should load");
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("reference fixture should compile");
    let definition =
        parse_definition(&artifacts.definition_kore).expect("emitted KORE should parse");

    let expected = oracle
        .heat_labels
        .into_iter()
        .map(|label| (label, oracle.heat_attributes.clone()))
        .chain(
            oracle
                .cool_labels
                .into_iter()
                .map(|label| (label, oracle.cool_attributes.clone())),
        )
        .collect::<std::collections::BTreeMap<_, _>>();
    let actual = definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| {
            let Sentence::Axiom { attributes, .. } = sentence else {
                return None;
            };
            let label = attributes.0.iter().find_map(|attribute| match attribute {
                Pattern::Application { symbol, arguments }
                    if symbol.name == "label"
                        && matches!(arguments.as_slice(), [Pattern::String(_)]) =>
                {
                    let [Pattern::String(label)] = arguments.as_slice() else {
                        unreachable!()
                    };
                    Some(label.as_utf8().unwrap().to_owned())
                }
                _ => None,
            })?;
            expected.contains_key(&label).then(|| {
                let mut names = attributes
                    .0
                    .iter()
                    .filter_map(|attribute| match attribute {
                        Pattern::Application { symbol, .. } => Some(symbol.name.clone()),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                names.sort();
                (label, names)
            })
        })
        .collect::<std::collections::BTreeMap<_, _>>();
    let expected = expected
        .into_iter()
        .map(|(label, names)| {
            let mut names = names
                .into_iter()
                .map(|name| kast::identifier::encode(&name))
                .collect::<Vec<_>>();
            names.sort();
            (label, names)
        })
        .collect::<std::collections::BTreeMap<_, _>>();

    assert_eq!(actual, expected);
}

macro_rules! declaration_snapshot {
    ($name:ident, $source:expr, $module:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let declarations = declaration_modules(&lowered(source, $module), $module)
                .expect("declarations should emit");
            let printer = Printer::pretty(120);
            let semantics = printer.print_module(&declarations.semantics);
            let syntax = printer.print_module(&declarations.syntax);
            assert_eq!(
                parse_module(&semantics).expect("semantic declarations should reparse"),
                declarations.semantics,
            );
            assert_eq!(
                parse_module(&syntax).expect("syntax declarations should reparse"),
                declarations.syntax,
            );
            let emitted = format!("// semantics\n{semantics}\n\n// syntax\n{syntax}");
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(emitted);
            });
        }
    };
}

macro_rules! module_snapshot {
    ($name:ident, $source:expr, $module:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let modules = module_to_kore(&rules(source, $module), $module)
                .expect("KORE modules should emit");
            let printer = Printer::pretty(100);
            let semantics = printer.print_module(&modules.semantics);
            let syntax = printer.print_module(&modules.syntax);
            let macros = modules
                .macros
                .iter()
                .map(|sentence| printer.print_sentence(sentence))
                .collect::<Vec<_>>()
                .join("\n\n");
            assert_eq!(
                parse_module(&semantics).expect("semantic module should reparse"),
                modules.semantics,
            );
            assert_eq!(
                parse_module(&syntax).expect("syntax module should reparse"),
                modules.syntax,
            );
            for (source, sentence) in macros.split("\n\n").zip(&modules.macros) {
                assert_eq!(
                    parse_sentence(source).expect("macro sentence should reparse"),
                    *sentence,
                );
            }
            let emitted = format!(
                "// semantics\n{semantics}\n\n// syntax\n{syntax}\n\n// macros\n{macros}"
            );
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(emitted);
            });
        }
    };
}

macro_rules! definition_snapshot {
    ($name:ident, $source:expr, $module:expr) => {
        #[test]
        fn $name() {
            let source = indoc!($source);
            let declarations = declaration_modules(&lowered(source, $module), $module)
                .expect("declarations should emit");
            let definition = declarations.semantics_definition();
            let emitted = Printer::pretty(100).print_definition(&definition);
            assert_eq!(
                parse_definition(&emitted).expect("complete definition should reparse"),
                definition,
            );
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_snapshot!(emitted);
            });
        }
    };
}

declaration_snapshot!(
    emits_sort_and_symbol_declarations,
    r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Exp
          syntax Bool

          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Exp "*" Exp [left, symbol(_*_)]
                       > Exp "+" Exp [left, symbol(_+_)]
                       | "box(" value:Int ")" [color(red), format(%1 %2 %3), symbol(box)]
          syntax Bool ::= Exp "==" Exp [function, hook(KEQUAL.eq), symbol(eq), total]
        endmodule
    "#,
    "MAIN"
);

#[test]
fn omits_syntax_relations_only_from_unlabeled_brackets() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "(" Exp ")" [bracket, color(red)]
                       | "[" Exp "]" [bracket, symbol(group)]
        endmodule
    "#};
    let declarations =
        declaration_modules(&lowered(source, "MAIN"), "MAIN").expect("declarations should emit");

    let attribute_names = |label: &str| {
        let encoded = encode_kore_label(&Label::new(label));
        declarations
            .syntax
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    symbol, attributes, ..
                } if symbol == &encoded => Some(
                    attributes
                        .0
                        .iter()
                        .filter_map(|attribute| match attribute {
                            Pattern::Application { symbol, .. } => Some(symbol.name.as_str()),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            })
            .expect("bracket symbol should be declared in the syntax module")
    };

    let unlabeled = attribute_names("(_)_MAIN_Exp_Exp");
    for retained in ["bracket", "colors", "format", "terminals"] {
        assert!(
            unlabeled.contains(&retained),
            "missing `{retained}` attribute"
        );
    }
    for relation in ["priorities", "left", "right"] {
        assert!(
            !unlabeled.contains(&relation),
            "unlabeled bracket retained `{relation}` attribute"
        );
    }

    let labeled = attribute_names("group");
    for relation in ["priorities", "left", "right"] {
        assert!(
            labeled.contains(&relation),
            "labeled bracket omitted `{relation}` attribute"
        );
    }

    // A bracket's label names only its syntax-module symbol: no term contains a bracket.
    let group = encode_kore_label(&Label::new("group"));
    assert!(
        !declarations
            .semantics
            .sentences
            .iter()
            .any(|sentence| matches!(
                sentence,
                Sentence::SymbolDeclaration { symbol, .. } if symbol == &group
            )),
        "labeled bracket was declared in the semantic module"
    );
}

#[test]
fn unit_attribute_naming_no_production_is_an_error() {
    let source = indoc! {r#"
        module MAIN
          syntax KItem
          syntax MyMap [hook(MAP.Map)]
          syntax MyMap ::= KItem "|->" KItem
            [function, hook(MAP.element), symbol(element)]
          syntax MyMap ::= MyMap MyMap
            [function, hook(MAP.concat), symbol(concat), unit(.MyMap), element(element)]
        endmodule
    "#};
    let error = declaration_modules(&lowered(source, "MAIN"), "MAIN")
        .expect_err("a collection label must resolve to exactly one production");
    assert_eq!(
        error.to_string(),
        "Expected to find exactly one production for KLabel: .MyMap found: 0"
    );
}

#[test]
fn schematic_labels_cannot_escape_through_symbol_attributes() {
    let source = indoc! {r#"
        module MAIN
          syntax Value
          syntax {S} Value ::= member(S) [symbol(member)]
          syntax Value ::= Value "join" Value [symbol(join), element(member)]
        endmodule
    "#};
    let error = declaration_modules(&lowered(source, "MAIN"), "MAIN")
        .expect_err("an attribute names one symbol, rather than a schematic family");
    let diagnostic = format!("{error:?}");
    assert!(
        diagnostic.contains("SchematicAttributeLabel"),
        "{diagnostic}"
    );
    assert!(diagnostic.contains("label: \"member\""), "{diagnostic}");
    assert!(
        diagnostic.contains(&format!("parameters: {:?}", [kast::Sort::new("S")])),
        "{diagnostic}"
    );
}

fn compiled_probe(source: &str, module: &str) -> k_rust::kore::ast::Definition {
    use k_rust::{
        builtin::embedded,
        kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
        outer::{LoadOptions, ResolvedSource, load_with_options},
    };

    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("collection-probe.k", source),
        module,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("collection probe should load");
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("collection probe should compile");
    parse_definition(&artifacts.definition_kore).expect("emitted KORE should parse")
}

fn assert_unit_instance(module: &k_rust::kore::ast::Module, expected: &str) {
    let printer = Printer::pretty(1000);
    let unit_axioms = module
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Axiom {
                pattern,
                attributes,
                ..
            } if attributes.0.iter().any(|attribute| {
                matches!(
                    attribute,
                    Pattern::Application { symbol, arguments }
                        if symbol.name == "unit" && arguments.is_empty()
                )
            }) =>
            {
                Some(printer.print_pattern(pattern))
            }
            _ => None,
        })
        .filter(|pattern| pattern.contains("Lblcat"))
        .collect::<Vec<_>>();
    assert_eq!(unit_axioms.len(), 2, "both unit axioms must be emitted");
    for axiom in unit_axioms {
        assert!(axiom.contains(expected), "{axiom}");
    }

    let unit_attribute = module
        .sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } if symbol.name == "Lblcat" => {
                attributes.0.iter().find_map(|attribute| match attribute {
                    Pattern::Application { symbol, arguments } if symbol.name == "unit" => {
                        let [instance] = arguments.as_slice() else {
                            panic!("unit attribute must name exactly one symbol instance");
                        };
                        Some(printer.print_pattern(instance))
                    }
                    _ => None,
                })
            }
            _ => None,
        })
        .expect("cat must carry a unit attribute");
    assert_eq!(unit_attribute, expected);
}

#[test]
fn schematic_function_unit_is_instantiated_at_the_naming_result_sort() {
    let source = indoc! {r#"
        module UNIT-PARAM-FN
          imports INT
          syntax {S} S ::= "eps" [symbol(eps)]
          syntax Foo ::= Int
          syntax Foo ::= Foo "++" Foo [symbol(cat), function, assoc, unit(eps)]
        endmodule
    "#};
    let definition = compiled_probe(source, "UNIT-PARAM-FN");
    let module = definition
        .modules
        .iter()
        .find(|module| module.name == "UNIT-PARAM-FN")
        .expect("main module should be emitted");
    assert_unit_instance(module, "Lbleps{SortFoo{}}()");
}

#[test]
fn schematic_unit_uses_the_naming_productions_binder() {
    let source = indoc! {r#"
        module MAIN
          syntax {T} Box{T}
          syntax {S} S ::= "eps" [symbol(eps)]
          syntax {T} Box{T} ::= Box{T} "++" Box{T}
            [symbol(cat), function, assoc, unit(eps)]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN")
        .expect("a unit can be instantiated with the naming production's own formals");
    assert_unit_instance(&modules.semantics, "Lbleps{SortBox{SortT}}()");
    for sentence in &modules.semantics.sentences {
        if let Sentence::Axiom {
            parameters,
            pattern,
            ..
        } = sentence
            && Printer::pretty(1000)
                .print_pattern(pattern)
                .contains("Lbleps{SortBox{SortT}}()")
        {
            assert!(parameters.iter().any(|parameter| parameter == "SortT"));
        }
    }
}

#[test]
fn map_ceil_instantiates_in_keys_from_the_closed_element_key_sort() {
    let source = indoc! {r#"
        module MAP-IK-PARAM
          syntax V
          syntax MyMap [hook(MAP.Map)]
          syntax MyMap ::= item(V, V) [function, hook(MAP.element), symbol(item)]
          syntax MyMap ::= ".MyMap" [function, hook(MAP.unit), symbol(unit)]
          syntax MyMap ::= MyMap MyMap
            [function, hook(MAP.concat), symbol(concat), element(item), unit(unit), assoc, comm]
          syntax {W} Bool ::= keys(W, MyMap) [function, hook(MAP.in_keys), symbol(keys)]
        endmodule
    "#};
    let definition = compiled_probe(source, "MAP-IK-PARAM");
    let module = definition
        .modules
        .iter()
        .find(|module| module.name == "MAP-IK-PARAM")
        .expect("main module should be emitted");
    let printer = Printer::pretty(1000);
    let map_ceil_axioms = module
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Axiom { pattern, .. } => Some(printer.print_pattern(pattern)),
            _ => None,
        })
        .filter(|pattern| pattern.contains("\\ceil{SortMyMap{}") && pattern.contains("Lblkeys"))
        .collect::<Vec<_>>();
    assert_eq!(map_ceil_axioms.len(), 1);
    assert!(
        map_ceil_axioms[0].contains("Lblkeys{SortV{}}"),
        "{}",
        map_ceil_axioms[0]
    );
}

#[test]
fn sort_heads_sharing_a_kore_name_are_an_error() {
    let error = declaration_modules(
        &lowered(
            "module MAIN\n  syntax MInt{8}\n  syntax MInt\nendmodule\n",
            "MAIN",
        ),
        "MAIN",
    )
    .expect_err("distinct sort heads must have distinct KORE names");
    assert_eq!(
        error.to_string(),
        "cannot emit sort declarations: the sorts MInt and MInt{S0} are both named SortMInt in KORE"
    );

    declaration_modules(
        &lowered("module MAIN\n  syntax MInt{8}\nendmodule\n", "MAIN"),
        "MAIN",
    )
    .expect("a single sort head should emit successfully");
}

#[test]
fn numeral_instance_arguments_of_any_length_have_nat_declarations() {
    let source = "module MAIN\n  syntax MInt{4294967296}\nendmodule\n";
    let declarations =
        declaration_modules(&lowered(source, "MAIN"), "MAIN").expect("declarations should emit");

    for module in [&declarations.semantics, &declarations.syntax] {
        let attributes = module
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SortDeclaration {
                    name,
                    parameters,
                    attributes,
                    ..
                } if name == "Sort4294967296" && parameters.is_empty() => Some(attributes),
                _ => None,
            })
            .expect("Sort4294967296 must be declared");
        assert!(attributes.0.iter().any(|attribute| matches!(attribute,
            Pattern::Application { symbol, arguments }
                if symbol.name == "nat"
                    && symbol.sort_parameters.is_empty()
                    && arguments == &[Pattern::String("4294967296".into())]
        )));
    }
}

#[test]
fn fu19_standalone_schematic_sort_emits_its_head_and_hook_in_both_modules() {
    for hooked in [false, true] {
        let attribute = if hooked { " [hook(MINT.MInt)]" } else { "" };
        let source = format!("module MAIN\n  syntax {{W}} MInt{{W}}{attribute}\nendmodule\n");
        let definition = rules(&source, "MAIN");
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.sort_catalog(resolved.main_module_id());
        assert!(
            catalog.all_sorts().is_empty(),
            "a schematic family selects no instance"
        );
        let modules = module_to_kore(&definition, "MAIN").expect("KORE modules should emit");
        for module in [&modules.semantics, &modules.syntax] {
            let declarations = module
                .sentences
                .iter()
                .filter_map(|sentence| match sentence {
                    Sentence::SortDeclaration {
                        hooked,
                        name,
                        parameters,
                        attributes,
                    } => Some((hooked, name, parameters, attributes)),
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(declarations.len(), 1, "only the MInt head is declared");
            let (actual_hooked, name, parameters, attributes) = declarations[0];
            assert_eq!(name, "SortMInt");
            assert_eq!(parameters.len(), 1);
            assert_eq!(*actual_hooked, hooked);
            let hooks = attributes
                .0
                .iter()
                .filter_map(|attribute| match attribute {
                    Pattern::Application { symbol, arguments } if symbol.name == "hook" => {
                        assert!(symbol.sort_parameters.is_empty());
                        Some(arguments.as_slice())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            if hooked {
                assert_eq!(hooks, vec![&[Pattern::String("MINT.MInt".into())][..]]);
            } else {
                assert!(hooks.is_empty());
            }
            assert!(
                !module
                    .sentences
                    .iter()
                    .any(|sentence| matches!(sentence, Sentence::SymbolDeclaration { .. })),
                "a schematic declaration invents no concrete-instance helpers"
            );
        }
    }
}

#[test]
fn fu19_unused_binders_preserve_ground_and_nullary_declarations() {
    for (body, expected) in [
        ("syntax {W} MInt{8}", vec![("Sort8", 0), ("SortMInt", 1)]),
        ("syntax {W} Foo", vec![("SortFoo", 0)]),
    ] {
        let source = format!("module MAIN\n  {body}\nendmodule\n");
        let modules =
            module_to_kore(&rules(&source, "MAIN"), "MAIN").expect("KORE modules should emit");
        for module in [&modules.semantics, &modules.syntax] {
            let declarations = module
                .sentences
                .iter()
                .filter_map(|sentence| match sentence {
                    Sentence::SortDeclaration {
                        hooked,
                        name,
                        parameters,
                        attributes,
                    } => {
                        assert!(!hooked);
                        if name == "Sort8" {
                            assert!(attributes.0.iter().any(|attribute| matches!(attribute,
                                Pattern::Application { symbol, arguments }
                                    if symbol.name == "nat"
                                        && symbol.sort_parameters.is_empty()
                                        && arguments == &[Pattern::String("8".into())]
                            )));
                        }
                        Some((name.as_str(), parameters.len()))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(declarations, expected);
        }
    }
}

#[test]
fn bracket_declarations_accept_klabel_objects_and_legacy_strings() {
    let source = indoc! {r#"
        module MAIN
          syntax {S} Box{S} ::= "(" Box{S} ")" [bracket]
        endmodule
    "#};

    for (representation, expected_parameter_count) in [
        (
            json!({
                "node": "KLabel",
                "name": "paren",
                "params": [{"node": "KSort", "name": "S", "params": []}],
            }),
            1,
        ),
        (json!("paren"), 1),
    ] {
        let mut definition = lowered(source, "MAIN");
        let bracket = definition.modules[0]
            .local_sentences
            .iter_mut()
            .find(|sentence| sentence.attributes().get("bracket").is_some())
            .expect("expected a bracket production");
        k_rust::definition::sentence_mut(bracket)
            .attributes_mut()
            .insert("bracketLabel", representation);

        let declarations = declaration_modules(&definition, "MAIN").unwrap();
        let symbol = declarations
            .syntax
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration { symbol, .. }
                    if symbol.name == encode_kore_label(&Label::new("paren")).name =>
                {
                    Some(symbol)
                }
                _ => None,
            })
            .expect("the structured bracket label should declare a syntax symbol");
        assert_eq!(symbol.sort_parameters.len(), expected_parameter_count);
    }
}

#[test]
fn embedded_priority_separator_labels_reach_syntax_relations_intact() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= Exp "|->" Exp [symbol(_|->_)]
                       | Exp Exp [symbol(_Map_)]
                       | ".Map" [symbol(.Map)]
          syntax priority _|->_ > _Map_ .Map
        endmodule
    "#};
    let declarations = declaration_modules(&lowered(source, "MAIN"), "MAIN").unwrap();
    let source_symbol = encode_kore_label(&Label::new("_|->_"));
    let priorities = declarations
        .syntax
        .sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::SymbolDeclaration {
                symbol, attributes, ..
            } if symbol == &source_symbol => attributes.0.iter().find_map(|attribute| {
                let Pattern::Application { symbol, arguments } = attribute else {
                    return None;
                };
                (symbol.name == "priorities").then_some(arguments)
            }),
            _ => None,
        })
        .expect("the source symbol should carry a priorities relation");
    let related = priorities
        .iter()
        .filter_map(|pattern| match pattern {
            Pattern::Application { symbol, .. } => Some(symbol.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(related.len(), 2);
    for label in ["_Map_", ".Map"] {
        assert!(related.contains(&encode_kore_label(&Label::new(label))));
    }
}

definition_snapshot!(
    wraps_generated_modules_in_the_standard_backend_definition,
    r#"
        module MAIN
          syntax GeneratedTopCell ::= "init"
            [function, initializer, symbol(initGeneratedTopCell)]
        endmodule
    "#,
    "MAIN"
);

declaration_snapshot!(
    emits_bracket_symbols_only_in_the_syntax_definition,
    r#"
        module MAIN
          syntax Exp ::= "value" [symbol(value)]
                       | "(" Exp ")" [bracket]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_ordinary_rewrite_rules_and_claims,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]
          syntax GeneratedTopCell ::= "<top>" Exp "</top>" [symbol(top)]

          rule <top> X:Exp + 0 </top> => <top> X:Exp </top>
            requires X:Exp == 0
            ensures X:Exp == 1
            [label(step), priority(42)]

          claim <top> X:Exp </top> => <top> ?Y:Exp </top>
            ensures ?Y:Exp == X:Exp
            [label(reachable)]

          claim <top> X:Exp </top>
            requires X:Exp == 0
            [label(invariant)]
        endmodule
    "#,
    "MAIN"
);

#[test]
fn emits_rewrite_and_claim_concrete_variables_as_kore_variables() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax GeneratedTopCell ::= "foo(" Int ")" [symbol(foo)]
                                    | "bar(" Int ")" [symbol(bar)]

          rule foo(X:Int) => bar(X:Int) [concrete(X), label(foo-rule)]
          claim foo(X:Int) => bar(X:Int) [symbolic(X), label(bar-claim)]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap();

    let attribute_argument = |label: &str, attribute_name: &str| {
        modules
            .semantics
            .sentences
            .iter()
            .find_map(|sentence| {
                let attributes = match sentence {
                    Sentence::Axiom { attributes, .. } => attributes,
                    Sentence::Claim { attributes, .. } => attributes,
                    _ => return None,
                };
                let has_label = attributes.0.iter().any(|attribute| {
                    matches!(
                        attribute,
                        Pattern::Application { symbol, arguments }
                            if symbol.name == "label"
                                && arguments == &[Pattern::String(label.into())]
                    )
                });
                if !has_label {
                    return None;
                }
                attributes.0.iter().find_map(|attribute| match attribute {
                    Pattern::Application { symbol, arguments } if symbol.name == attribute_name => {
                        arguments.first()
                    }
                    _ => None,
                })
            })
            .expect("the requested rule attribute should be emitted")
    };

    for (label, attribute_name) in [("foo-rule", "concrete"), ("bar-claim", "symbolic")] {
        assert_eq!(
            attribute_argument(label, attribute_name),
            &Pattern::Variable(k_rust::kore::ast::Variable {
                kind: k_rust::kore::ast::VariableKind::Element,
                name: "VarX".into(),
                sort: encode_kore_sort(&k_rust::kast::Sort::new("Int")),
            })
        );
    }
}

#[test]
fn rejects_concrete_variable_not_free_on_rewrite_lhs() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax GeneratedTopCell ::= "foo(" Int ")" [symbol(foo)]
                                    | "bar(" Int ")" [symbol(bar)]

          rule foo(X:Int) => bar(Y:Int) [concrete(Y)]
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert!(
        error
            .to_string()
            .contains("concrete attribute refers to missing free variable")
    );
}

#[test]
fn rejects_non_rewrite_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax GeneratedTopCell ::= "<top>" Int "</top>" [symbol(top)]

          rule <top> 0 </top> [label(stutter)]
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();

    assert_eq!(error.to_string(), "cannot emit rule without a rewrite body");
}

module_snapshot!(
    emits_function_anywhere_and_simplification_equations,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= Exp "+" Exp [symbol(_+_)]
          syntax Exp ::= "inc(" Exp ")" [function, symbol(inc)]
          syntax Exp ::= "double(" Exp ")" [symbol(double)]
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]

          rule inc(X:Exp + 0) => X:Exp
            requires X:Exp == 1
            ensures X:Exp == 2
            [label(eval-inc)]

          rule X:Exp + 0 => X:Exp
            [simplification, label(plus-zero)]

          rule double(X:Exp + 0) => double(X:Exp)
            [anywhere, label(double-zero)]

          claim inc(X:Exp) => X:Exp
            [label(inc-claim)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_owise_equations_with_refreshed_competitors,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= "choose(" Exp "," Exp ")" [function, symbol(choose)]
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]

          rule choose(0, Y:Exp) => Y:Exp
            [label(left-zero)]

          rule choose(X:Exp, 0) => X:Exp
            requires X:Exp == 1
            [label(right-zero)]

          rule choose(X:Exp, Y:Exp) => X:Exp
            requires X:Exp == Y:Exp
            [label(equal-arguments)]

          rule choose(1, Z:Exp) => Z:Exp
            [non-executable, label(ignored-non-executable)]

          rule choose(A:Exp, B:Exp) => A:Exp
            [simplification, label(ignored-simplification)]

          rule choose(_Gen0:Exp, Y:Exp) => Y:Exp
            requires _Gen0:Exp == Y:Exp
            [owise, label(otherwise)]
        endmodule
    "#,
    "MAIN"
);

#[test]
fn emits_owise_competitors_as_a_right_nested_binary_disjunction() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "choose(" Exp ")" [function, symbol(choose)]

          rule choose(a) => a [label(choose-a)]
          rule choose(b) => b [label(choose-b)]
          rule choose(X:Exp) => X:Exp [owise, label(otherwise)]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap();
    let owise = modules
        .semantics
        .sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Axiom {
                pattern,
                attributes,
                ..
            } => attributes
                .0
                .iter()
                .any(|attribute| {
                    matches!(
                        attribute,
                        Pattern::Application { symbol, arguments }
                            if symbol.name == "label"
                                && arguments == &[Pattern::String("otherwise".into())]
                    )
                })
                .then_some(pattern.as_ref()),
            _ => None,
        })
        .expect("the owise equation should be emitted");
    let Pattern::Implies { left, .. } = owise else {
        panic!("owise equation should be an implication")
    };
    let Pattern::And { arguments, .. } = left.as_ref() else {
        panic!("owise equation should conjoin its match conditions")
    };
    let disjunction = arguments
        .iter()
        .find_map(|argument| match argument {
            Pattern::Not { argument, .. } => Some(argument.as_ref()),
            _ => None,
        })
        .expect("the owise equation should negate its competitors");

    let mut disjunction = disjunction;
    let mut competitors = 0;
    loop {
        match disjunction {
            Pattern::Or { arguments, .. } => {
                assert_eq!(arguments.len(), 2, "KORE disjunctions must be binary");
                competitors += 1;
                disjunction = &arguments[1];
            }
            Pattern::Bottom { .. } => break,
            pattern => panic!("right-nested disjunction must end in bottom, found {pattern:?}"),
        }
    }
    assert_eq!(competitors, 2);
}

module_snapshot!(
    routes_macro_and_alias_axioms_to_the_standalone_sentence_list,
    r#"
        module MAIN
          syntax Exp ::= "done(" Exp ")" [symbol(done)]
          syntax Exp ::= "plain(" Exp ")" [symbol(plain)]
          syntax Exp ::= "macro(" Exp ")" [macro, symbol(macro)]
          syntax Exp ::= "macroRec(" Exp ")" [macro-rec, symbol(macroRec)]
          syntax Exp ::= "alias(" Exp ")" [alias, symbol(alias)]
          syntax Exp ::= "aliasRec(" Exp ")" [alias-rec, symbol(aliasRec)]
          syntax Exp ::= "functionMacro(" Exp ")" [function, macro, symbol(functionMacro)]

          rule macro(X:Exp) => done(X:Exp)
          rule macroRec(X:Exp) => done(X:Exp)
          rule alias(X:Exp) => done(X:Exp)
          rule aliasRec(X:Exp) => done(X:Exp)
          rule functionMacro(X:Exp) => done(X:Exp)
          rule plain(X:Exp) => done(X:Exp) [macro, priority(17)]
          rule macro(done(X:Exp)) => X:Exp [simplification]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    a_labelled_token_production_is_neither_a_constructor_nor_in_no_confusion,
    r#"
        module MAIN
          syntax Str ::= r"[a-z]+" [token, symbol(strLit)]
          syntax Str ::= r"[A-Z]+" [token, symbol(idLit)]
          syntax Exp ::= "wrap(" Str ")" [symbol(wrap)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_one_path_and_all_path_reachability_claims,
    r#"
        module MAIN [all-path]
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Bool ::= Exp "==" Exp [function, symbol(eq)]
          syntax GeneratedTopCell ::= "<top>" Exp "</top>" [symbol(top)]

          claim <top> X:Exp </top> => <top> ?Y:Exp </top>
            requires X:Exp == 0
            ensures ?Y:Exp == X:Exp
            [one-path, label(one-step)]

          claim <top> X:Exp </top> => <top> X:Exp </top>
            [all-path, label(all-step)]

          claim <top> X:Exp </top> => <top> X:Exp </top>
            [label(module-default)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    propagates_impurity_through_function_dependencies,
    r#"
        module MAIN
          syntax Exp ::= "done" [symbol(done)]
          syntax Exp ::= "source" [function, impure, symbol(source)]
          syntax Exp ::= "middle" [function, symbol(middle)]
          syntax Exp ::= "top" [function, symbol(top)]
          syntax Exp ::= "clean" [function, symbol(clean)]
          syntax Exp ::= "guarded" [function, symbol(guarded)]
          syntax Bool ::= "isDone(" Exp ")" [function, symbol(isDone)]
          syntax Exp ::= "impureAnywhere(" Exp ")" [impure, symbol(impureAnywhere)]
          syntax Exp ::= "usesAnywhere" [function, symbol(usesAnywhere)]
          syntax Exp ::= "macroAnywhere(" Exp ")" [impure, symbol(macroAnywhere)]
          syntax Exp ::= "usesMacroAnywhere" [function, symbol(usesMacroAnywhere)]

          rule source => done
          rule middle => source
          rule top => middle
          rule clean => done
          rule guarded => done requires isDone(source)
          rule impureAnywhere(X:Exp) => X:Exp [anywhere]
          rule usesAnywhere => impureAnywhere(done)
          rule macroAnywhere(X:Exp) => X:Exp [anywhere, macro]
          rule usesMacroAnywhere => macroAnywhere(done)
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_subsort_and_overload_axioms,
    r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Number ::= Int
          syntax Value ::= Number
          syntax K ::= Value

          syntax Int ::= "narrow(" Int ")" [overload(project), symbol(narrow)]
          syntax Number ::= "wide(" Number ")" [overload(project), symbol(wide)]
          syntax Value ::= "widest(" Value ")" [overload(project), symbol(widest)]

          syntax Value ::= "asInt(" Int ")" [overload(view), symbol(asInt)]
          syntax Value ::= "asNumber(" Number ")" [overload(view), symbol(asNumber)]

          syntax Int ::= "fromInt(" Int ")" [overload(promote), symbol(fromInt)]
          syntax Number ::= "fromNumber(" Int ")" [overload(promote), symbol(fromNumber)]
        endmodule
    "#,
    "MAIN"
);

/// `injective` is an axiom of the emitted theory, so it is declared only for productions whose
/// equations cannot identify two applications with different arguments.
#[test]
fn declares_injective_only_where_no_equation_can_identify_applications() {
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)]
                       | "s(" Nat ")" [symbol(s)]
          syntax Number ::= Nat
          syntax Value ::= Number
          syntax K ::= Value

          syntax Value ::= "wrap(" Nat ")" [symbol(wrap)]
          rule wrap(s(X:Nat)) => wrap(X:Nat) [anywhere]

          syntax Nat ::= "narrow(" Nat ")" [overload(project), symbol(narrow)]
          syntax Number ::= "wide(" Number ")" [overload(project), symbol(wide)]

          syntax Nat ::= "low(" Nat ")" [overload(collapse), symbol(low)]
          syntax Number ::= "middle(" Number ")" [overload(collapse), symbol(middle)]
          syntax Value ::= "high(" Value ")" [overload(collapse), symbol(high)]
          rule low(s(X:Nat)) => low(X:Nat) [anywhere]

          syntax Value ::= "expand(" Nat ")" [macro, symbol(expand)]
          rule expand(X:Nat) => wrap(X:Nat)
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").expect("KORE modules should emit");
    let declared = |module: &k_rust::kore::ast::Module, symbol: &str| {
        module
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    symbol: declared,
                    attributes,
                    ..
                } if declared.name == symbol => Some(attributes.0.iter().any(|attribute| {
                    matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "injective")
                })),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{symbol} should be declared"))
    };
    for module in [&modules.semantics, &modules.syntax] {
        // Constructors, and an overload family whose only equations lower to them.
        for symbol in ["Lblz", "Lbls", "Lblnarrow", "Lblwide"] {
            assert!(declared(module, symbol), "{symbol} in {}", module.name);
        }
        // An anywhere head (`wrap(s(z)) = wrap(z)`), every production above an anywhere-ruled
        // lesser production (`middle(s(z)) = middle(z)`, transitively `high`), and a macro head.
        for symbol in ["Lblwrap", "Lbllow", "Lblmiddle", "Lblhigh", "Lblexpand"] {
            assert!(!declared(module, symbol), "{symbol} in {}", module.name);
        }
    }
}

/// What an emitted declaration states about the totality of an equation head.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HeadClaim {
    /// `functional{}()` on the declaration and the functional axiom in the semantic module.
    Functional,
    /// Neither, and `function{}()`: a partial function evaluated by its equations.
    PartialFunction,
    /// Neither, and `function{}(), value-production{}(), anywhere{}()`: normal forms are values.
    PartialValueProduction,
    /// Neither, and `function{}(), value-production{}(), macro{}()`: residual expansion head.
    PartialMacroProduction,
}

/// Compiles `source` through the normal pipeline, asserts each symbol's declared claims in the
/// semantic and the syntax definition, and returns the semantic definition loaded by the backend.
fn assert_equation_head_functional(
    source: &str,
    symbols: &[(&str, HeadClaim)],
) -> k_rust_backend::definition::BackendDefinition {
    let mut resolver = |_: &str, required: &str| {
        k_rust::builtin::embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = outer::load_with_options(
        outer::ResolvedSource::new("equation-totality.k", source),
        "A",
        &mut resolver,
        &outer::LoadOptions {
            implicit_sources: vec![k_rust::builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                k_rust::kompile::CompilationBackend::Rust
                    .excluded_module_attribute()
                    .into(),
            ],
            ..outer::LoadOptions::default()
        },
    )
    .expect("equation-totality probe should load");
    let artifacts = k_rust::kompile::compile_loaded_definition(
        &loaded,
        k_rust::kompile::CompileOptions::default(),
    )
    .expect("equation-totality probe should compile");
    let semantics = parse_definition(&artifacts.definition_kore).unwrap();
    let syntax = parse_definition(&artifacts.syntax_definition_kore).unwrap();
    let has_functional = |attributes: &k_rust::kore::ast::Attributes| {
        attributes.0.iter().any(|attribute| {
            matches!(attribute, Pattern::Application { symbol, arguments }
                if symbol.name == "functional" && arguments.is_empty())
        })
    };
    for &(name, claim) in symbols {
        for definition in [&semantics, &syntax] {
            let module = definition
                .modules
                .iter()
                .find(|module| module.name == "A")
                .expect("probe module A should be emitted in both definitions");
            let actual = module
                .sentences
                .iter()
                .find_map(|sentence| match sentence {
                    Sentence::SymbolDeclaration {
                        symbol, attributes, ..
                    } if symbol.name == name => Some(attributes),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("{name} should be declared in {}", module.name));
            let has = |attribute_name: &str| {
                actual.0.iter().any(|attribute| {
                    matches!(attribute, Pattern::Application { symbol, arguments }
                        if symbol.name == attribute_name
                            && symbol.sort_parameters.is_empty()
                            && arguments.is_empty())
                })
            };
            assert_eq!(
                has_functional(actual),
                claim == HeadClaim::Functional,
                "{name} functional declaration in {}",
                module.name
            );
            assert_eq!(
                has("function"),
                // A source function declared `total` carries both claims.
                claim != HeadClaim::Functional || has("total"),
                "{name} function declaration in {}",
                module.name
            );
            assert_eq!(
                has("value-production"),
                matches!(
                    claim,
                    HeadClaim::PartialValueProduction | HeadClaim::PartialMacroProduction
                ),
                "{name} value-production declaration in {}",
                module.name
            );
            match claim {
                HeadClaim::PartialValueProduction => assert!(
                    has("anywhere"),
                    "{name} partial equation head without anywhere in {}",
                    module.name
                ),
                HeadClaim::PartialMacroProduction => assert!(
                    has("macro"),
                    "{name} partial macro head without macro in {}",
                    module.name
                ),
                HeadClaim::Functional | HeadClaim::PartialFunction => {}
            }
        }
        let functional_axiom = semantics.modules.iter().flat_map(|module| &module.sentences).any(|sentence| {
            let Sentence::Axiom { pattern, attributes, .. } = sentence else {
                return false;
            };
            let Pattern::Exists { variable, body, .. } = pattern.as_ref() else {
                return false;
            };
            let Pattern::Equals { left, right, .. } = body.as_ref() else {
                return false;
            };
            has_functional(attributes)
                && matches!(left.as_ref(), Pattern::Variable(value) if value == variable.as_ref())
                && matches!(right.as_ref(), Pattern::Application { symbol, .. } if symbol.name == name)
        });
        assert_eq!(
            functional_axiom,
            claim == HeadClaim::Functional,
            "{name} functional axiom"
        );
    }
    k_rust_backend::definition::BackendDefinition::internalize(&semantics, "A")
        .expect("emitted partial declarations should load in the backend")
}

#[test]
fn an_anywhere_equation_with_a_partial_rhs_withholds_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax S ::= mk(Int) [symbol(mk)] | wrap(Int) [symbol(wrap)]
          rule wrap(X) => mk(X /Int 0) requires X ==Int 0 [anywhere]
        endmodule
    "#},
        &[("Lblwrap", HeadClaim::PartialValueProduction)],
    );
}

#[test]
fn an_anywhere_equation_with_a_defined_rhs_keeps_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax S ::= mk(Int) [symbol(mk)] | wrap(Int) [symbol(wrap)]
          rule wrap(X) => mk(X +Int 1) requires X ==Int 0 [anywhere]
        endmodule
    "#},
        &[("Lblwrap", HeadClaim::Functional)],
    );
}

/// The compile-corpus case `anywhere2`: `foo(a) = foo(b)` reapplies its own head, so the least
/// fixed point gives no evidence and `foo` stays a partial equation head.
#[test]
fn a_self_referential_anywhere_equation_withholds_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Base ::= A | B
          syntax Foo ::= foo(Base) [symbol(foo)]
          rule foo(a => b) [anywhere]
        endmodule
    "#},
        &[("Lblfoo", HeadClaim::PartialValueProduction)],
    );
}

#[test]
fn anywhere_equations_with_injected_rhs_preserve_the_arguments_definedness() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax Exp ::= Int
                       | wrap(Int) [symbol(wrap)]
                       | partialWrap(Int) [symbol(partialWrap)]
          rule wrap(X) => X +Int 1 [anywhere]
          rule partialWrap(X) => X /Int 0 [anywhere]
        endmodule
    "#},
        &[
            ("Lblwrap", HeadClaim::Functional),
            ("LblpartialWrap", HeadClaim::PartialValueProduction),
        ],
    );
}

#[test]
fn an_overload_equation_with_a_partial_lesser_withholds_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax Exp ::= Int
          syntax Exp ::= fe(Exp) [symbol(fE), overload(f)]
          syntax Int ::= fi(Int) [symbol(fI), overload(f), function]
          rule fi(I) => I /Int 0
        endmodule
    "#},
        &[
            ("LblfE", HeadClaim::PartialValueProduction),
            ("LblfI", HeadClaim::PartialFunction),
        ],
    );
}

#[test]
fn a_declared_total_overload_greater_over_a_partial_lesser_keeps_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax Exp ::= Int
          syntax Exp ::= fe(Exp) [symbol(fE), overload(f), function, total]
          syntax Int ::= fi(Int) [symbol(fI), overload(f), function]
          rule fi(I) => I /Int 0
          rule fe(E) => E
        endmodule
    "#},
        &[
            ("LblfE", HeadClaim::Functional),
            ("LblfI", HeadClaim::PartialFunction),
        ],
    );
}

#[test]
fn a_constructor_only_overload_chain_keeps_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          syntax Digit
          syntax Small ::= Digit
          syntax Medium ::= Small
          syntax Large ::= Medium
          syntax K ::= Large
          syntax Small ::= narrow(Small) [overload(project), symbol(narrow)]
          syntax Medium ::= wide(Medium) [overload(project), symbol(wide)]
          syntax Large ::= widest(Large) [overload(project), symbol(widest)]
          syntax Large ::= asSmall(Small) [overload(view), symbol(asSmall)]
          syntax Large ::= asMedium(Medium) [overload(view), symbol(asMedium)]
          syntax Small ::= fromSmall(Small) [overload(promote), symbol(fromSmall)]
          syntax Medium ::= fromMedium(Small) [overload(promote), symbol(fromMedium)]
        endmodule
    "#},
        &[
            ("Lblwide", HeadClaim::Functional),
            ("Lblwidest", HeadClaim::Functional),
            ("LblasMedium", HeadClaim::Functional),
            ("LblfromMedium", HeadClaim::Functional),
        ],
    );
}

#[test]
fn a_macro_expansion_with_a_partial_rhs_withholds_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax S ::= mk(Int) [symbol(mk)] | half(Int) [symbol(half), macro]
          rule half(X) => mk(X /Int 0)
        endmodule
    "#},
        &[("Lblhalf", HeadClaim::PartialMacroProduction)],
    );
}

#[test]
fn an_alias_expansion_with_a_partial_rhs_withholds_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax S ::= mk(Int) [symbol(mk)] | half(Int) [symbol(half), alias]
          rule half(X) => mk(X /Int 0)
        endmodule
    "#},
        &[("Lblhalf", HeadClaim::PartialMacroProduction)],
    );
}

#[test]
fn a_macro_expansion_with_a_defined_rhs_keeps_functional() {
    assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax S ::= mk(Int) [symbol(mk)] | next(Int) [symbol(next), macro]
          rule next(X) => mk(X +Int 1)
        endmodule
    "#},
        &[("Lblnext", HeadClaim::Functional)],
    );
}

/// A head whose `functional` the judgement withholds loads as a partial symbol with the role
/// the backend gives a declaration that carries only the same equation marker: an anywhere head
/// (`wrap`, the self-referential `foo`, the overload-greater `fE`) stays an equation head, whose
/// normal-form applications are values of its sort, and a macro head stays residual.
#[test]
fn partial_emitted_heads_load_with_the_roles_of_unclaimed_equation_heads() {
    use k_rust_backend::term::{FunctionType, HeadRole, SymbolType};
    let definition = assert_equation_head_functional(
        indoc! {r#"
        module A
          imports INT
          syntax S ::= mk(Int) [symbol(mk)]
                     | wrap(Int) [symbol(wrap)]
                     | half(Int) [symbol(half), macro]
          rule wrap(X) => mk(X /Int 0) [anywhere]
          rule half(X) => mk(X /Int 0)
          syntax Exp ::= Int
          syntax Exp ::= fe(Exp) [symbol(fE), overload(f)]
          syntax Int ::= fi(Int) [symbol(fI), overload(f), function]
          rule fi(I) => I /Int 0
          syntax A ::= "a" [symbol(a)]
          syntax B ::= "b" [symbol(b)]
          syntax Base ::= A | B
          syntax Foo ::= foo(Base) [symbol(foo)]
          rule foo(a => b) [anywhere]
        endmodule
        "#},
        &[
            ("Lblwrap", HeadClaim::PartialValueProduction),
            ("Lblhalf", HeadClaim::PartialMacroProduction),
            ("LblfE", HeadClaim::PartialValueProduction),
            ("LblfI", HeadClaim::PartialFunction),
            ("Lblfoo", HeadClaim::PartialValueProduction),
        ],
    );
    // The declarations a definition states for a head with no claim and only its equation
    // marker, which the backend reads as partial equation heads.
    let unclaimed = k_rust_backend::definition::BackendDefinition::internalize(
        &parse_definition(
            r"[]
            module MAIN
              sort SortS{} []
              symbol anywhereHead{}(SortS{}) : SortS{} [anywhere{}()]
              symbol macroHead{}(SortS{}) : SortS{} [macro{}()]
            endmodule []",
        )
        .unwrap(),
        "MAIN",
    )
    .expect("unclaimed equation heads should load");
    let unclaimed_role = |name: &str| {
        let attributes = &unclaimed.symbols[name].attributes;
        assert_eq!(
            attributes.symbol_type,
            SymbolType::Function(FunctionType::Partial),
            "{name}"
        );
        attributes.head_role()
    };
    assert_eq!(unclaimed_role("anywhereHead"), HeadRole::EquationHead);
    assert_eq!(unclaimed_role("macroHead"), HeadRole::Residual);
    for (name, unclaimed_head) in [
        ("Lblwrap", "anywhereHead"),
        ("Lblfoo", "anywhereHead"),
        ("LblfE", "anywhereHead"),
        ("Lblhalf", "macroHead"),
    ] {
        let attributes = &definition.symbols[name].attributes;
        assert_eq!(
            attributes.symbol_type,
            SymbolType::Function(FunctionType::Partial),
            "{name} backend symbol type"
        );
        assert_eq!(
            attributes.head_role(),
            unclaimed_role(unclaimed_head),
            "{name} backend head role"
        );
    }
}

/// A macro-like rule on a production without a macro attribute is the emitted equation
/// `plain(X) = done(X)`, so `plain` is not a free constructor: declaring it `constructor` with
/// no-confusion axioms against `done` would make the theory inconsistent. The same holds when
/// the rule's left side covers only some arguments (`part(z) = done(z)`), whose other
/// applications survive expansion and so are not declared `macro` either.
#[test]
fn a_production_rewritten_by_a_macro_rule_is_not_a_constructor() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "z" [symbol(z)]
          syntax Exp ::= "done(" Exp ")" [symbol(done)]
          syntax Exp ::= "plain(" Exp ")" [symbol(plain)]
          syntax Exp ::= "part(" Exp ")" [symbol(part)]
          syntax Exp ::= "other(" Exp ")" [symbol(other)]

          rule plain(X:Exp) => done(X:Exp) [macro]
          rule part(z) => done(z) [alias]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").expect("KORE modules should emit");
    let attributes = |module: &k_rust::kore::ast::Module, symbol: &str| {
        module
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    symbol: declared,
                    attributes,
                    ..
                } if declared.name == symbol => Some(
                    attributes
                        .0
                        .iter()
                        .filter_map(|attribute| match attribute {
                            Pattern::Application { symbol, .. } => Some(symbol.name.to_string()),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{symbol} should be declared"))
    };
    for module in [&modules.semantics, &modules.syntax] {
        for symbol in ["Lblz", "Lbldone", "Lblother"] {
            let attributes = attributes(module, symbol);
            assert!(
                attributes.iter().any(|name| name == "constructor"),
                "{symbol} in {}: {attributes:?}",
                module.name
            );
        }
        for symbol in ["Lblplain", "Lblpart"] {
            let attributes = attributes(module, symbol);
            for absent in ["constructor", "injective", "macro"] {
                assert!(
                    !attributes.iter().any(|name| name == absent),
                    "{symbol} in {} carries {absent}: {attributes:?}",
                    module.name
                );
            }
            assert!(
                attributes.iter().any(|name| name == "functional"),
                "{symbol} in {}: {attributes:?}",
                module.name
            );
        }
    }
    let printer = Printer::compact();
    let no_confusion = modules
        .semantics
        .sentences
        .iter()
        .filter(|sentence| {
            matches!(sentence, Sentence::Axiom { attributes, .. }
                if attributes.0.iter().any(|attribute| matches!(attribute,
                    Pattern::Application { symbol, .. } if symbol.name == "constructor")))
        })
        .map(|sentence| printer.print_sentence(sentence))
        .collect::<Vec<_>>();
    assert!(
        no_confusion
            .iter()
            .any(|axiom| axiom.contains("Lbldone") && axiom.contains("Lblother")),
        "{no_confusion:#?}"
    );
    for axiom in &no_confusion {
        if axiom.contains("\\not") || axiom.contains("\\implies") {
            assert!(
                !axiom.contains("Lblplain") && !axiom.contains("Lblpart"),
                "{axiom}"
            );
        }
    }
}

/// An alias `P #as V` matches exactly the terms `P` matches and binds `V` to the whole term, so
/// it leaves the symbol that heads a rule's left side unchanged. `wrap(X) #as _V => done(X)
/// [anywhere]` is the equation `wrap(X) = done(X)` and `plain(X) #as _W => done(X) [macro]` the
/// macro axiom `plain(X) = done(X)`, so neither head is a free constructor: declaring either
/// `constructor` or `injective`, or stating its disjointness from `done`, would contradict its
/// own equation.
#[test]
fn an_aliased_rule_head_heads_its_equation() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "z" [symbol(z)]
          syntax Exp ::= "done(" Exp ")" [symbol(done)]
          syntax Exp ::= "wrap(" Exp ")" [symbol(wrap)]
          syntax Exp ::= "plain(" Exp ")" [symbol(plain)]

          rule wrap(X:Exp) #as _V:Exp => done(X:Exp) [anywhere]
          rule plain(X:Exp) #as _W:Exp => done(X:Exp) [macro]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").expect("KORE modules should emit");
    let attributes = |module: &k_rust::kore::ast::Module, symbol: &str| {
        module
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    symbol: declared,
                    attributes,
                    ..
                } if declared.name == symbol => Some(
                    attributes
                        .0
                        .iter()
                        .filter_map(|attribute| match attribute {
                            Pattern::Application { symbol, .. } => Some(symbol.name.to_string()),
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                ),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{symbol} should be declared"))
    };
    for module in [&modules.semantics, &modules.syntax] {
        for symbol in ["Lblz", "Lbldone"] {
            let attributes = attributes(module, symbol);
            assert!(
                attributes.iter().any(|name| name == "constructor"),
                "{symbol} in {}: {attributes:?}",
                module.name
            );
        }
        for symbol in ["Lblwrap", "Lblplain"] {
            let attributes = attributes(module, symbol);
            for absent in ["constructor", "injective"] {
                assert!(
                    !attributes.iter().any(|name| name == absent),
                    "{symbol} in {} carries {absent}: {attributes:?}",
                    module.name
                );
            }
        }
    }
    let printer = Printer::compact();
    for sentence in &modules.semantics.sentences {
        let Sentence::Axiom { attributes, .. } = sentence else {
            continue;
        };
        if attributes.0.iter().any(|attribute| {
            matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == "constructor")
        }) {
            // The no-confusion axioms; the no-junk axiom still lists both as generators.
            let axiom = printer.print_sentence(sentence);
            if axiom.contains("\\not") || axiom.contains("\\implies") {
                assert!(
                    !axiom.contains("Lblwrap") && !axiom.contains("Lblplain"),
                    "{axiom}"
                );
            }
        }
    }
}

module_snapshot!(
    emits_algebraic_axioms,
    r#"
        module MAIN
          syntax Exp ::= ".Exp" [function, symbol(.Exp)]
          syntax Exp ::= Exp "++" Exp
            [assoc, comm, function, idem, symbol(_++_), unit(.Exp)]
          syntax Exp ::= Exp "~" Exp [symbol(_~_), unit(.Exp)]

          syntax {S} Box{S}
          syntax {S} Box{S} ::= Box{S} "merge" Box{S}
            [assoc, idem, symbol(merge)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_comm_axiom_for_non_function_productions,
    r#"
        module MAIN
          syntax Exp ::= Exp "&&&" Exp [comm, symbol(c3)]
          syntax Exp ::= Exp "+++" Exp [function, comm, symbol(p3)]
          syntax Exp ::= ".E" [symbol(dotE)]
            | Exp "**" Exp [assoc, unit(dotE), symbol(s2)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_functional_axioms,
    r#"
        module MAIN
          syntax Exp ::= "zero" [symbol(zero)]
          syntax Exp ::= "pair(" Exp "," Exp ")" [symbol(pair)]
          syntax Exp ::= "partial(" Exp ")" [function, symbol(partial)]
          syntax Exp ::= "total(" Exp ")" [function, symbol(total), total]

          syntax {S} Box{S}
          syntax {S} Box{S} ::= "box(" S ")" [symbol(box)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_constructor_no_confusion_axioms,
    r#"
        module MAIN
          syntax Exp ::= "zero" [symbol(zero)]
          syntax Exp ::= "one" [symbol(one)]
          syntax Exp ::= "wrap(" Exp ")" [symbol(wrap)]
          syntax Exp ::= "pair(" Exp "," Exp ")" [symbol(pair)]
          syntax Exp ::= "evaluate(" Exp ")" [function, symbol(evaluate)]
          syntax Exp ::= Exp "++" Exp [assoc, symbol(_++_)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    emits_sort_no_junk_axioms,
    r#"
        module MAIN
          syntax Atom ::= r"[a-z]+" [token]
          syntax Exp ::= Atom
          syntax Exp ::= "zero" [symbol(zero)]
          syntax Exp ::= "pair(" Exp "," Exp ")" [symbol(pair)]
          syntax Exp ::= "evaluate(" Exp ")" [function, symbol(evaluate)]
          syntax Exp ::= "expand(" Exp ")" [macro, symbol(expand)]
          syntax Empty
          syntax TokenSort [token]
          syntax K ::= Exp
        endmodule
    "#,
    "MAIN"
);

fn assert_axiom_sort_variables_are_bound(sentences: &[Sentence]) {
    for sentence in sentences {
        if let Sentence::Axiom {
            parameters,
            pattern,
            attributes,
        } = sentence
        {
            let mut variables = pattern.sort_variables();
            for attribute in &attributes.0 {
                variables.extend(attribute.sort_variables());
            }
            assert!(
                variables.iter().all(|name| parameters.contains(name)),
                "unbound sort variables {variables:?} in {}",
                Printer::compact().print_sentence(sentence)
            );
        }
    }
}

fn disjointness_pair(sentences: &[Sentence], left: &str, right: &str) -> Vec<String> {
    sentences
        .iter()
        .filter(|sentence| {
            matches!(sentence, Sentence::Axiom { pattern, .. }
            if matches!(pattern.as_ref(), Pattern::Not { .. })
                && pattern.find_application(|symbol, _| symbol.name == left).is_some()
                && pattern.find_application(|symbol, _| symbol.name == right).is_some())
        })
        .map(|sentence| Printer::compact().print_sentence(sentence))
        .collect()
}

#[test]
fn disjointness_unifies_a_closed_result_with_a_parametric_constructor() {
    let source = indoc! {r#"
        module MAIN
          syntax A
          syntax {W} MInt{W}
          syntax MInt{A}
          syntax MInt{A} ::= "ka" [symbol(ka)]
          syntax {W} MInt{W} ::= "mk" [symbol(mk)]
        endmodule
    "#};
    let modules = module_to_kore(&lowered(source, "MAIN"), "MAIN").unwrap();
    assert_eq!(
        disjointness_pair(&modules.semantics.sentences, "Lblka", "Lblmk"),
        [
            r"axiom{} \not{SortMInt{SortA{}}}(\and{SortMInt{SortA{}}}(Lblka{}(), Lblmk{SortA{}}())) [constructor{}()]"
        ]
    );
    assert_axiom_sort_variables_are_bound(&modules.semantics.sentences);
    assert_axiom_sort_variables_are_bound(&modules.syntax.sentences);
}

#[test]
fn disjointness_renames_independent_formals_before_unifying_results() {
    for (result, argument, remaining) in [("W", "V", "SortV'1"), ("V", "W", "SortW'1")] {
        let source = format!(
            r#"module MAIN
              syntax {{W}} MInt{{W}}
              syntax {{W}} MInt{{W}} ::= "mk" [symbol(mk)]
              syntax {{W, V}} MInt{{{result}}} ::= "mk2(" {argument} ")" [symbol(mk2)]
            endmodule"#
        );
        let modules = module_to_kore(&lowered(&source, "MAIN"), "MAIN").unwrap();
        let symbol_parameters = if result == "W" {
            format!("SortW, {remaining}")
        } else {
            format!("{remaining}, SortW")
        };
        let mut parameters = [remaining, "SortW"];
        parameters.sort();
        let parameters = parameters.join(", ");
        assert_eq!(
            disjointness_pair(&modules.semantics.sentences, "Lblmk", "Lblmk2"),
            [format!(
                r"axiom{{{parameters}}} \not{{SortMInt{{SortW}}}}(\and{{SortMInt{{SortW}}}}(Lblmk{{SortW}}(), Lblmk2{{{symbol_parameters}}}(Y0:{remaining}))) [constructor{{}}()]"
            )]
        );
        assert_axiom_sort_variables_are_bound(&modules.semantics.sentences);
        assert_axiom_sort_variables_are_bound(&modules.syntax.sentences);
    }
}

#[test]
fn disjointness_omits_constructors_at_non_unifying_closed_results() {
    let source = indoc! {r#"
        module MAIN
          syntax A
          syntax B
          syntax {W} MInt{W}
          syntax MInt{A} ::= "ka" [symbol(ka)]
          syntax MInt{B} ::= "kb" [symbol(kb)]
        endmodule
    "#};
    let modules = module_to_kore(&lowered(source, "MAIN"), "MAIN").unwrap();
    assert_eq!(
        disjointness_pair(&modules.semantics.sentences, "Lblka", "Lblkb"),
        Vec::<String>::new()
    );
    assert_axiom_sort_variables_are_bound(&modules.semantics.sentences);
    assert_axiom_sort_variables_are_bound(&modules.syntax.sentences);
}

#[cfg(feature = "z3-inference")]
#[test]
fn disjointness_result_instance_fixture_binds_every_axiom_sort_variable() {
    let prelude = embedded("prelude.md").unwrap();
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(
            "result-instance.k",
            include_str!("fixtures/sort-check/result-instance.k"),
        ),
        "RESULT-INSTANCE",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    for kore in [
        &artifacts.definition_kore,
        &artifacts.syntax_definition_kore,
    ] {
        let definition = parse_definition(kore).unwrap();
        for module in &definition.modules {
            assert_axiom_sort_variables_are_bound(&module.sentences);
        }
    }
}

#[test]
fn disjointness_binds_phantom_symbol_parameters_independently() {
    let source = indoc! {r#"
        module MAIN
          syntax A
          syntax {W} MInt{W}
          syntax {P} MInt{A} ::= "ka" [symbol(ka)]
          syntax {P} MInt{A} ::= "kb" [symbol(kb)]
        endmodule
    "#};
    let modules = module_to_kore(&lowered(source, "MAIN"), "MAIN").unwrap();
    assert_eq!(
        disjointness_pair(&modules.semantics.sentences, "Lblka", "Lblkb"),
        [
            r"axiom{SortP, SortP'1} \not{SortMInt{SortA{}}}(\and{SortMInt{SortA{}}}(Lblka{SortP}(), Lblkb{SortP'1}())) [constructor{}()]"
        ]
    );
    assert_axiom_sort_variables_are_bound(&modules.semantics.sentences);
    assert_axiom_sort_variables_are_bound(&modules.syntax.sentences);
}

module_snapshot!(
    labelled_token_productions_contribute_only_top_to_no_junk,
    r#"
        module MAIN
          syntax Str ::= r"[a-z]+" [token, symbol(strLit)]
          syntax Str ::= r"[A-Z]+" [token, symbol(idLit)]
          syntax Exp ::= "wrap(" Str ")" [symbol(wrap)]
        endmodule
    "#,
    "MAIN"
);

module_snapshot!(
    labelled_token_productions_contribute_only_top_to_no_junk_in_reverse_order,
    r#"
        module MAIN
          syntax Str ::= r"[A-Z]+" [token, symbol(idLit)]
          syntax Str ::= r"[a-z]+" [token, symbol(strLit)]
          syntax Exp ::= "wrap(" Str ")" [symbol(wrap)]
        endmodule
    "#,
    "MAIN"
);

/// The printed axioms of the semantic module whose top pattern is a disjunction over `sort`:
/// the sort's no-junk axiom.
///
/// The selection ignores whitespace, so an axiom the printer breaks across lines is selected too.
fn no_junk_axioms_of(source: &str, sort: &str) -> Vec<String> {
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").expect("KORE modules should emit");
    let printer = Printer::pretty(100);
    let prefix = format!(r"axiom{{}}\or{{{sort}}}(");
    modules
        .semantics
        .sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Axiom { .. }))
        .map(|sentence| printer.print_sentence(sentence))
        .filter(|printed| {
            printed
                .split_whitespace()
                .collect::<String>()
                .starts_with(&prefix)
        })
        .collect()
}

#[test]
fn a_cell_map_key_projection_emits_totality_only_for_a_sole_cell_generator() {
    for (schema, expected_attributes, expected_functional_axioms) in [
        (
            "syntax {S} S ::= wrap(S) [symbol(wrap)]",
            "[function{}()]",
            0,
        ),
        ("", "[function{}(), functional{}(), total{}()]", 1),
    ] {
        let source = format!(
            r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              {schema}
              configuration <items> <item multiplicity="*" type="Map"> <id> 0 </id> </item> </items>
              syntax K
              syntax Map
            endmodule
            "#
        );
        let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
        let loaded = outer::load(
            outer::ResolvedSource::new("cell-map.k", &source),
            "MAIN",
            &mut resolver,
        )
        .expect("cell-map configuration should load and expand");
        let definition = k_rust::kompile::generate_sort_predicate_syntax(&loaded.into_definition())
            .expect("sort predicate syntax should generate");
        let definition = k_rust::kompile::generate_sort_projections(&definition)
            .expect("cell-map key totality should be judged");
        let definition = k_rust::kompile::concretize_cells(&definition)
            .expect("generated cell rules should have their declared arities");
        let definition = k_rust::kompile::subsort_kitem(&definition)
            .expect("generated projections should have their KItem subsort paths");
        let modules = module_to_kore(&definition, "MAIN").expect("KORE modules should emit");
        let printer = Printer::compact();
        let declaration = modules
            .semantics
            .sentences
            .iter()
            .find(|sentence| {
                matches!(sentence, Sentence::SymbolDeclaration { symbol, .. }
                    if symbol.name == "LblItemCellMapKey")
            })
            .expect("cell-map key symbol should be declared");
        let expected = format!(
            "symbol LblItemCellMapKey{{}}(SortItemCell{{}}) : SortIdCell{{}} {expected_attributes}"
        );
        assert_eq!(
            printer
                .print_sentence(declaration)
                .split_whitespace()
                .collect::<String>(),
            expected.split_whitespace().collect::<String>(),
            "schema {schema:?}",
        );
        let functional_axioms = modules
            .semantics
            .sentences
            .iter()
            .filter(|sentence| {
                let Sentence::Axiom { attributes, .. } = sentence else {
                    return false;
                };
                attributes.0.iter().any(|attribute| {
                    matches!(attribute, Pattern::Application { symbol, .. }
                        if symbol.name == "functional")
                }) && printer
                    .print_sentence(sentence)
                    .contains("LblItemCellMapKey{}(")
            })
            .count();
        assert_eq!(
            functional_axioms, expected_functional_axioms,
            "schema {schema:?}"
        );
    }
}

#[test]
fn a_sort_polymorphic_generator_is_listed_after_the_sorts_own_generators() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "g" [symbol(g)]
          syntax {S} S ::= wrap(S) [symbol(wrap)]
        endmodule
    "#};
    let axioms = no_junk_axioms_of(source, "SortFoo{}")
        .into_iter()
        .map(|axiom| axiom.split_whitespace().collect::<String>())
        .collect::<Vec<_>>();
    assert_eq!(
        axioms,
        vec![concat!(
            r"axiom{}\or{SortFoo{}}(Lblg{}(),",
            r"\exists{SortFoo{}}(X0:SortFoo{},Lblwrap{SortFoo{}}(X0:SortFoo{})),",
            r"\bottom{SortFoo{}}())[constructor{}()]",
        )]
    );
}

#[test]
fn a_polymorphic_result_parameter_named_like_a_sort_has_no_disjointness_pairing() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "g" [symbol(g)]
          syntax {Foo} Foo ::= w(Foo) [symbol(w)]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN").expect("KORE modules should emit");
    let printer = Printer::compact();
    let disjoint_pairs = modules
        .semantics
        .sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Axiom { .. }))
        .map(|sentence| printer.print_sentence(sentence))
        .filter(|axiom| {
            axiom.contains(r"\not") && axiom.contains("Lblg{") && axiom.contains("Lblw{")
        })
        .collect::<Vec<_>>();
    assert_eq!(disjoint_pairs, Vec::<String>::new());
    let axioms = no_junk_axioms_of(source, "SortFoo{}")
        .into_iter()
        .map(|axiom| axiom.split_whitespace().collect::<String>())
        .collect::<Vec<_>>();
    assert_eq!(
        axioms,
        vec![concat!(
            r"axiom{}\or{SortFoo{}}(Lblg{}(),",
            r"\exists{SortFoo{}}(X0:SortFoo{},Lblw{SortFoo{}}(X0:SortFoo{})),",
            r"\bottom{SortFoo{}}())[constructor{}()]",
        )]
    );
}

#[test]
fn token_productions_contribute_only_top_to_no_junk_in_any_order() {
    // Property: a token production parses to domain values, which no symbol generates, so no
    // no-junk axiom lists a token production's symbol, and the axiom of a sort does not depend
    // on the order of its token productions.
    let lower_first = indoc! {r#"
        module MAIN
          syntax Str ::= r"[a-z]+" [token, symbol(strLit)]
          syntax Str ::= r"[A-Z]+" [token, symbol(idLit)]
          syntax Str ::= r"[0-9]+" [token]
          syntax Exp ::= "wrap(" Str ")" [symbol(wrap)]
        endmodule
    "#};
    let upper_first = indoc! {r#"
        module MAIN
          syntax Str ::= r"[0-9]+" [token]
          syntax Str ::= r"[A-Z]+" [token, symbol(idLit)]
          syntax Str ::= r"[a-z]+" [token, symbol(strLit)]
          syntax Exp ::= "wrap(" Str ")" [symbol(wrap)]
        endmodule
    "#};
    let expected = vec![
        r"axiom{} \or{SortStr{}}(\top{SortStr{}}(), \bottom{SortStr{}}()) [constructor{}()]"
            .to_owned(),
    ];
    assert_eq!(no_junk_axioms_of(lower_first, "SortStr{}"), expected);
    assert_eq!(no_junk_axioms_of(upper_first, "SortStr{}"), expected);
}

#[test]
fn a_sort_with_a_generator_leaving_a_sort_parameter_free_gets_no_no_junk_axiom() {
    // Property: `pick{W}` is a value of `Foo` for every sort `W`, so no finite disjunction lists
    // `Foo`'s values and `Foo` gets no no-junk axiom, whether `W` occurs in an argument or nowhere;
    // `Bar`, whose generator is closed, keeps its axiom.
    let open = indoc! {r#"
        module MAIN
          syntax {W} MInt{W} [hook(MINT.MInt)]
          syntax Bar ::= "b" [symbol(b)]
          syntax {W} Foo ::= pick(MInt{W}, Bar) [symbol(pick)]
          syntax Foo ::= "g" [symbol(g)]
        endmodule
    "#};
    let phantom = indoc! {r#"
        module MAIN
          syntax {W} MInt{W} [hook(MINT.MInt)]
          syntax Bar ::= "b" [symbol(b)]
          syntax {W} Foo ::= pick(Bar) [symbol(pick)]
          syntax Foo ::= "g" [symbol(g)]
        endmodule
    "#};
    let bar = vec![
        r"axiom{} \or{SortBar{}}(Lblb{}(), \bottom{SortBar{}}()) [constructor{}()]".to_owned(),
    ];
    for source in [open, phantom] {
        assert_eq!(
            no_junk_axioms_of(source, "SortFoo{}"),
            Vec::<String>::new(),
            "{source}"
        );
        assert_eq!(no_junk_axioms_of(source, "SortBar{}"), bar, "{source}");
    }
}

#[test]
fn rejects_non_binary_associative_productions() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "single(" Exp ")" [assoc, symbol(single)]
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit assoc axiom for production #0: expected arity 2, found 1"
    );
}

#[test]
fn rejects_ill_sorted_associative_productions() {
    let source = indoc! {r#"
        module MAIN
          syntax Small ::= "mix(" Small "," Large ")" [assoc, symbol(mix)]
          syntax Large
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit assoc axiom for production #0: the result sort must be a subsort of both argument sorts"
    );
}

#[test]
fn rejects_ill_sorted_idempotent_productions() {
    let source = indoc! {r#"
        module MAIN
          syntax Small ::= "merge(" Small "," Large ")" [idem, symbol(merge)]
          syntax Large
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit idem axiom for production #0: the result and both argument sorts must be equal"
    );
}

#[test]
fn rejects_non_binary_commutative_productions() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "single(" Exp ")" [comm, symbol(single)]
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit comm axiom for production #0: expected arity 2, found 1"
    );
}

#[test]
fn rejects_ill_sorted_commutative_productions() {
    let source = indoc! {r#"
        module MAIN
          syntax Small ::= "mix(" Small "," Large ")" [comm, symbol(mix)]
          syntax Large
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit comm axiom for production #0: both argument sorts must be equal"
    );
}

#[test]
fn rejects_injective_algebraic_productions() {
    for attribute in ["assoc", "comm", "idem"] {
        for function in ["", "function, "] {
            let source = format!(
                r#"
                module MAIN
                  syntax Exp ::= Exp "mix" Exp [{function}{attribute}, injective, symbol(mix)]
                endmodule
                "#
            );
            let error = module_to_kore(&rules(&source, "MAIN"), "MAIN").unwrap_err();
            assert_eq!(
                error.to_string(),
                format!(
                    "cannot emit {attribute} axiom for production #0: injective contradicts the {attribute} axiom, which identifies applications with different arguments"
                ),
                "{source}"
            );
        }
    }
}

#[test]
fn rejects_non_binary_function_units() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= ".Exp" [function, symbol(.Exp)]
          syntax Exp ::= "wrap(" Exp ")" [function, symbol(wrap), unit(.Exp)]
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit unit axiom for production #1: expected arity 2, found 1"
    );
}

#[test]
fn rejects_ill_sorted_function_units() {
    let source = indoc! {r#"
        module MAIN
          syntax Small ::= ".Small" [function, symbol(.Small)]
          syntax Small ::= Small "join" Large
            [function, symbol(join), unit(.Small)]
          syntax Large
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot emit unit axiom for production #1: the result and both argument sorts must be equal"
    );
}

#[test]
fn rejects_non_top_cell_semantic_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          rule 0 => 1
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "ordinary semantic rules must rewrite GeneratedTopCell, found Int in rule #token(\"0\",\"Int\")=>#token(\"1\",\"Int\")"
    );
}

#[test]
fn rejects_existential_variables_in_equations() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          syntax Exp ::= "inc(" Exp ")" [function, symbol(inc)]
          rule inc(X:Exp) => ?Y:Exp
        endmodule
    "#};
    let error = module_to_kore(&rules(source, "MAIN"), "MAIN").unwrap_err();
    assert_eq!(
        error.to_string(),
        "cannot encode equations with existential variables: ?Y"
    );
}

declaration_snapshot!(
    emits_visible_imported_declarations_in_declaration_order,
    r#"
        module BASE
          syntax Atom ::= "atom" [symbol(atom)]
        endmodule

        module MAIN
          imports BASE
          syntax Result ::= "wrap" Atom [symbol(wrap)]
          syntax Result ::= "done" [symbol(done)]
        endmodule
    "#,
    "MAIN"
);

#[test]
fn rebases_imported_rule_productions_into_the_target_module_catalog() {
    let source = indoc! {r#"
        module BASE
          syntax Int ::= r"[0-9]+" [token]
          syntax GeneratedTopCell ::= "<top>" Int "</top>" [symbol(top)]
          rule <top> 0 </top> => <top> 1 </top>
        endmodule

        module MAIN
          imports BASE
          syntax Extra ::= "extra" [symbol(extra)]
        endmodule
    "#};
    let modules = module_to_kore(&rules(source, "MAIN"), "MAIN")
        .expect("imported rule metadata should rebase before KORE emission");
    let semantics = Printer::pretty(100).print_module(&modules.semantics);

    assert_eq!(
        parse_module(&semantics).expect("semantic module should reparse"),
        modules.semantics
    );
    assert!(
        semantics.contains("Lbltop") && semantics.contains("\\rewrites"),
        "the imported rewrite should be emitted: {semantics}"
    );
}

declaration_snapshot!(
    emits_parametric_declarations,
    r#"
        module MAIN
          syntax {S} Box{S}
          syntax {S} Box{S} ::= "box(" S ")" [symbol(box)]
        endmodule
    "#,
    "MAIN"
);

declaration_snapshot!(
    derives_hooked_collection_sort_attributes,
    r#"
        module MAIN
          syntax Map [hook(MAP.Map)]
          syntax MapItem
          syntax MapItem ::= "item" [symbol(MapItem)]
          syntax Map ::= ".Map" [function, hook(MAP.unit), symbol(.Map), total]
          syntax Map ::= Map Map [element(MapItem), symbol(_Map_), unit(.Map)]
        endmodule
    "#,
    "MAIN"
);

#[test]
fn backend_dispatched_namespaces_are_emitted_as_real_hooks() {
    #[derive(Deserialize)]
    struct Manifest {
        backend_namespaces: Vec<String>,
    }

    let manifest: Manifest = toml::from_str(include_str!("fixtures/hook-capabilities.toml"))
        .expect("hook capability manifest must be valid TOML");
    let mut source = "module MAIN\n  syntax Value\n".to_owned();
    for (index, namespace) in manifest.backend_namespaces.iter().enumerate() {
        source.push_str(&format!(
            "  syntax Value ::= \"probe{index}\" [function, hook({namespace}.probe), symbol(probe{index})]\n"
        ));
    }
    source.push_str("endmodule\n");
    let declarations = declaration_modules(&lowered(&source, "MAIN"), "MAIN").unwrap();

    for module in [&declarations.semantics, &declarations.syntax] {
        for (index, namespace) in manifest.backend_namespaces.iter().enumerate() {
            let label = format!("probe{index}");
            let hook = format!("{namespace}.probe");
            let symbol = encode_kore_label(&Label::new(&label));
            let (hooked, attributes) = module
                .sentences
                .iter()
                .find_map(|sentence| match sentence {
                    Sentence::SymbolDeclaration {
                        hooked,
                        symbol: declared,
                        attributes,
                        ..
                    } if declared == &symbol => Some((*hooked, attributes)),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("missing declaration for {label}"));
            assert!(hooked, "{hook} was emitted as an ordinary symbol");
            assert!(
                attributes.0.iter().any(|attribute| matches!(
                    attribute,
                    Pattern::Application { symbol, arguments }
                        if symbol.name == "hook"
                            && arguments == &[Pattern::String(hook.clone().into())]
                )),
                "{label} dropped hook({hook})"
            );
        }
    }
}

#[test]
fn plugin_hook_namespaces_are_hooked_only_when_admitted() {
    let source = indoc! {r#"
        module MAIN
          syntax Bytes
          syntax String
          syntax String ::= "keccak(" Bytes ")"
            [function, hook(KRYPTO.keccak256), symbol(keccak)]
          syntax Bytes ::= "concat(" Bytes "," Bytes ")"
            [function, hook(BYTES.concat), symbol(concat)]
        endmodule
    "#};
    let resolved = ResolvedDefinition::resolve(&lowered(source, "MAIN")).unwrap();
    let hooked = |namespaces: &[&str], label: &str| {
        let namespaces = namespaces
            .iter()
            .map(|namespace| (*namespace).to_owned())
            .collect::<Vec<_>>();
        let declarations =
            declaration_modules_from_resolved_with_options(&resolved, "MAIN", &namespaces).unwrap();
        let symbol = encode_kore_label(&Label::new(label));
        [&declarations.semantics, &declarations.syntax].map(|module| {
            module
                .sentences
                .iter()
                .find_map(|sentence| match sentence {
                    Sentence::SymbolDeclaration {
                        hooked,
                        symbol: declared,
                        attributes,
                        ..
                    } if declared == &symbol => Some((
                        *hooked,
                        attributes.0.iter().any(|attribute| {
                            matches!(
                                attribute,
                                Pattern::Application { symbol, .. } if symbol.name == "hook"
                            )
                        }),
                    )),
                    _ => None,
                })
                .unwrap_or_else(|| panic!("missing declaration for {label}"))
        })
    };

    // Java's fixed builtin namespaces are hooked regardless of the plugin allow-list.
    assert_eq!(hooked(&[], "concat"), [(true, true), (true, true)]);
    // A plugin namespace is an ordinary symbol until `--hook-namespaces` admits it.
    assert_eq!(hooked(&[], "keccak"), [(false, false), (false, false)]);
    assert_eq!(hooked(&["KRYPTO"], "keccak"), [(true, true), (true, true)]);
    assert_eq!(
        hooked(&["HASH"], "keccak"),
        [(false, false), (false, false)]
    );
}

#[test]
fn out_of_catalog_hook_namespaces_are_not_emitted_as_hooked_symbols() {
    let source = indoc! {r#"
        module MAIN
          syntax Value
          syntax Value ::= "probe"
            [function, hook(NOTANAMESPACE.probe), symbol(probe)]
        endmodule
    "#};
    let declarations = declaration_modules(&lowered(source, "MAIN"), "MAIN").unwrap();
    let symbol = encode_kore_label(&Label::new("probe"));

    for module in [&declarations.semantics, &declarations.syntax] {
        let (hooked, attributes) = module
            .sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::SymbolDeclaration {
                    hooked,
                    symbol: declared,
                    attributes,
                    ..
                } if declared == &symbol => Some((*hooked, attributes)),
                _ => None,
            })
            .expect("missing probe declaration");
        assert!(!hooked, "unknown hook namespace emitted as hooked-symbol");
        assert!(
            !attributes.0.iter().any(|attribute| matches!(
                attribute,
                Pattern::Application { symbol, .. } if symbol.name == "hook"
            )),
            "unknown hook attribute survived ordinary-symbol emission"
        );
    }
}

#[test]
fn encodes_labels_and_parametric_sorts() {
    assert_eq!(
        encode_kore_label(&kast::Label::new("inj")).to_string(),
        "inj{}"
    );
    let label = kast::Label::with_parameters("box(_)", vec![kast::Sort::new("S")]);
    assert_eq!(
        encode_kore_label(&label).to_string(),
        "Lblbox'LParUndsRPar'{SortS{}}"
    );
    let sort = kast::Sort::with_parameters(
        "Map",
        vec![kast::Sort::new("Key"), kast::Sort::new("Value")],
    );
    assert_eq!(
        encode_kore_sort(&sort).to_string(),
        "SortMap{SortKey{}, SortValue{}}"
    );
}

#[test]
fn round_trips_compiler_produced_kore_identifiers() {
    let names = [
        "plain-ASCII9",
        "éα",
        "😀",
        "_é+😀z",
        "\0\n\u{7f}",
        "module",
        "endmodule",
        "sort",
        "hooked-sort",
        "symbol",
        "hooked-symbol",
        "alias",
        "axiom",
    ];

    for name in names {
        let label = Label::new(name);
        let pattern = Pattern::Application {
            symbol: encode_kore_label(&label),
            arguments: Vec::new(),
        };
        assert_eq!(
            convert(&pattern).expect("compiler-produced label should convert"),
            kast::Term::Apply {
                label,
                arguments: Vec::new(),
            },
            "label {name:?}",
        );
    }
}

#[test]
fn round_trips_compiler_produced_kore_sort_identifiers() {
    let sort = kast::Sort::with_parameters(
        "é😀_",
        vec![
            kast::Sort::new("module"),
            kast::Sort::with_parameters("#Foo", vec![kast::Sort::new("α")]),
        ],
    );
    assert_eq!(
        convert_sort(&encode_kore_sort(&sort)).expect("compiler-produced sort should convert"),
        sort,
    );
}

#[test]
fn round_trips_variables_through_the_public_term_converters() {
    let definition = lowered("module MAIN\n  syntax #Foo\nendmodule", "MAIN");
    let resolved = ResolvedDefinition::resolve(&definition).expect("definition should resolve");
    let converter = TermConverter::new(&resolved, "MAIN").expect("converter should build");

    for name in ["Vé😀_", "@module"] {
        let variable = kast::Term::Variable {
            name: name.into(),
            sort: Some(kast::Sort::new("#Foo")),
        };
        let pattern = converter
            .convert(&variable)
            .expect("variable should convert to KORE");
        assert_eq!(
            convert(&pattern).expect("compiler-produced variable should convert to KAST"),
            variable,
            "variable {name:?}",
        );
    }
}

#[test]
fn parsed_hash_sort_round_trips_through_kore() {
    let definition = lowered(
        r#"
module MAIN
  syntax #Foo
endmodule
"#,
        "MAIN",
    );
    let source_sort = definition
        .main_module()
        .expect("main module should exist")
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            k_rust::definition::Sentence::SyntaxSort { sort, .. } if sort.name == "#Foo" => {
                Some(sort)
            }
            _ => None,
        })
        .expect("parsed #Foo declaration should lower");
    let encoded = encode_kore_sort(source_sort);
    assert_eq!(encoded.to_string(), "Sort'Hash'Foo{}");
    assert_eq!(
        convert_sort(&encoded).expect("parsed source sort should convert from KORE"),
        *source_sort,
    );
}

#[test]
fn decoded_sort_names_drive_hook_lookup() {
    let sort = kast::Sort::new("#String");
    let pattern = Pattern::DomainValue {
        sort: encode_kore_sort(&sort),
        value: "line\n".into(),
    };
    let hooks = std::collections::HashMap::from([("#String".into(), "STRING.String".into())]);
    assert_eq!(
        Converter::new(&hooks)
            .convert(&pattern)
            .expect("encoded hooked sort should convert"),
        kast::Term::Token {
            token: "\"line\\n\"".into(),
            sort,
        },
    );
}

#[test]
fn rejects_malformed_utf16_in_kore_identifiers() {
    for name in ["Lbl'd83d'", "Lbl'de00'", "Lbl'd83dSpce'"] {
        let pattern = Pattern::Application {
            symbol: k_rust::kore::ast::Symbol {
                name: name.into(),
                sort_parameters: Vec::new(),
            },
            arguments: Vec::new(),
        };
        let error = convert(&pattern).expect_err("malformed UTF-16 should be rejected");
        assert!(
            error.to_string().contains("invalid UTF-16"),
            "unexpected error for {name:?}: {error}",
        );
    }
}

/// `ModuleToKORE.convertSpecificationModule` emits `spec.sentencesExcept(definition)`: every
/// claim visible from the specification module that the definition module does not already
/// contain, not only the specification module's local claims.
#[cfg(feature = "z3-inference")]
#[test]
fn emits_claims_imported_into_the_specification_module() {
    let source = indoc!(
        r#"
        module DEF
          syntax State ::= "a" [symbol(a)]
                         | "b" [symbol(b)]
          configuration <k> $PGM:State </k>
          rule <k> a => b </k>
        endmodule

        module LEMMAS
          imports DEF
          claim [reach]: <k> a => b </k>
        endmodule

        module SPEC
          imports LEMMAS
        endmodule
        "#
    );
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("spec.k", source),
        "SPEC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("two-module specification should load");
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            default_claims_to_all_path: true,
            check_mode: CheckMode::Proof {
                definition_module: "DEF".into(),
            },
            ..CompileOptions::default()
        },
    )
    .expect("two-module specification should compile");
    let definition =
        parse_definition(&artifacts.definition_kore).expect("emitted KORE should parse");

    let spec = definition
        .modules
        .iter()
        .find(|module| module.name == "SPEC")
        .expect("the specification module should be emitted");
    let claim_labels = spec
        .sentences
        .iter()
        .filter_map(|sentence| {
            let Sentence::Claim { attributes, .. } = sentence else {
                return None;
            };
            attributes.0.iter().find_map(|attribute| match attribute {
                Pattern::Application { symbol, arguments } if symbol.name == "label" => {
                    let [Pattern::String(label)] = arguments.as_slice() else {
                        return None;
                    };
                    Some(label.clone())
                }
                _ => None,
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(claim_labels, ["LEMMAS.reach"]);
}

/// A source claim over a definition whose rules instantiate `!` variables says nothing about the
/// generated counter: the emitted claim rewrites an arbitrary initial counter to an existential
/// final one, so the claim gains one universal and one more leading `\exists`.
#[cfg(feature = "z3-inference")]
#[test]
fn claims_rewrite_the_generated_counter_to_an_existential() {
    let source = indoc!(
        r#"
        module DEF
          imports INT
          syntax State ::= "start" [symbol(start)]
                         | st(Int) [symbol(st)]
          configuration <k> $PGM:State </k>
          rule <k> start => st(!N:Int) </k>
        endmodule

        module SPEC
          imports DEF
          claim [fresh-value]: <k> start => st(?B:Int) </k>
        endmodule
        "#
    );
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("spec.k", source),
        "SPEC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![
                CompilationBackend::Rust.excluded_module_attribute().into(),
            ],
            ..LoadOptions::default()
        },
    )
    .expect("specification should load");
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            check_mode: CheckMode::Proof {
                definition_module: "DEF".into(),
            },
            ..CompileOptions::default()
        },
    )
    .expect("specification should compile");
    let definition =
        parse_definition(&artifacts.definition_kore).expect("emitted KORE should parse");
    let spec = definition
        .modules
        .iter()
        .find(|module| module.name == "SPEC")
        .expect("the specification module should be emitted");
    let printer = Printer::pretty(100);
    let claims = spec
        .sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Claim { pattern, .. } => Some(printer.print_pattern(pattern)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(claims.len(), 1);
    insta::assert_snapshot!(claims[0]);
}
