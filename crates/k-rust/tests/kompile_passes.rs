// Standard-prelude fixtures require native Z3 inference; their semantic assertions are
// feature-gated below. inner_rules::portable_build_rejects_the_standard_prelude covers
// the portable boundary instead of duplicating that rejection for each fixture.

use indoc::indoc;
#[cfg(feature = "z3-inference")]
use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    kore::{
        ast::{Pattern as KorePattern, Sentence as KoreSentence},
        parser::parse_definition,
    },
    outer::{LoadOptions, load_with_options},
};
use k_rust::{
    definition::{
        Attributes, Definition, FlatImport, FlatModule, LabelHead, ProductionId, ProductionItem,
        ResolvedDefinition, SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE,
        Sentence, checks::check_definition,
    },
    kast::{Label, ResolvedProductionId, Sort, Term, TermMetadata, TermSpan, printer::Printer},
    kompile::{
        GeneratedVariableIdentity, add_cool_like_attributes, add_implicit_computation_cell,
        add_semantics_module, add_sort_injections_to_definition, check_simplification_rules,
        concretize_cells, concretize_cells_in_sentence, constant_fold, expand_macros,
        expand_macros_in_term, generate_sort_predicate_rules, generate_sort_predicate_syntax,
        generate_sort_projections, guard_or_patterns, minimize_term_construction, module_to_kore,
        number_sentences, propagate_macro_attributes, remove_unit, resolve_anon_vars,
        resolve_anon_vars_in_sentence, resolve_comm, resolve_config_var, resolve_contexts,
        resolve_fresh_config_constants, resolve_fresh_constants, resolve_fun,
        resolve_function_with_config, resolve_heat_cool_attributes, resolve_io,
        resolve_semantic_casts, resolve_semantic_casts_in_sentence,
        resolve_semantic_casts_with_predicates_in_sentence, resolve_strict, subsort_kitem,
        term_to_kore,
    },
    outer::{ResolvedSource, load},
    provenance::{GeneratingPass, ORIGIN_ATTRIBUTE, ProvenanceLink, SourceId},
};
#[cfg(feature = "z3-inference")]
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

fn parsed(source: &str) -> k_rust::definition::Definition {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    load(
        ResolvedSource::new("definition.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap()
    .definition
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct ParametricIdOracle {
    rule: Vec<ParametricRuleId>,
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct ParametricRuleId {
    line: usize,
    unique_id: String,
}

/// UNIQUE_ID of every source rule of a compiled reference fixture, keyed by its Location line.
#[cfg(feature = "z3-inference")]
fn fixture_rule_ids(file_name: &str, source: &str, main_module: &str) -> BTreeMap<usize, String> {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(file_name, source),
        main_module,
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

    let attribute = |attributes: &k_rust::kore::ast::Attributes, name: &str| {
        attributes.0.iter().find_map(|attribute| match attribute {
            KorePattern::Application { symbol, arguments }
                if symbol.name == name
                    && matches!(arguments.as_slice(), [KorePattern::String(_)]) =>
            {
                let [KorePattern::String(value)] = arguments.as_slice() else {
                    unreachable!()
                };
                Some(value.clone())
            }
            _ => None,
        })
    };
    let source_suffix = format!("{file_name})");
    definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .filter_map(|sentence| {
            let KoreSentence::Axiom { attributes, .. } = sentence else {
                return None;
            };
            let source = attribute(
                attributes,
                "org'Stop'kframework'Stop'attributes'Stop'Source",
            )?;
            source.ends_with(&source_suffix).then(|| {
                let location = attribute(
                    attributes,
                    "org'Stop'kframework'Stop'attributes'Stop'Location",
                )
                .expect("source rule should have a location");
                let line = location
                    .strip_prefix("Location(")
                    .and_then(|location| location.split(',').next())
                    .and_then(|line| line.parse().ok())
                    .expect("source rule location should start with its line");
                (
                    line,
                    attribute(attributes, "UNIQUE'Unds'ID")
                        .expect("source rule should have a unique id"),
                )
            })
        })
        .collect()
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_parametric_fixture_rule_ids_match() {
    // reference: k/result/bin/kompile --backend haskell --main-module PARAMETRIC test.k
    let oracle: ParametricIdOracle = toml::from_str(include_str!(
        "fixtures/reference/kompile/parametric/reference.toml"
    ))
    .expect("reference id oracle should parse");
    let actual = fixture_rule_ids(
        "parametric.k",
        include_str!("fixtures/reference/kompile/parametric/test.k"),
        "PARAMETRIC",
    );
    let expected = oracle
        .rule
        .into_iter()
        .map(|rule| (rule.line, rule.unique_id))
        .collect::<BTreeMap<_, _>>();

    assert_eq!(actual, expected);
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_rewrite_list_singleton_rule_ids_match() {
    // reference: k/result/bin/kompile --backend haskell --main-module REWRITE-LIST-SINGLETON
    //   --syntax-module REWRITE-LIST-SINGLETON test.k
    //
    // The issue-1573 regression: NumberSentences
    // hashes the rule as the parser completed it, so the UNIQUE_ID of `<v> 1 => foo(1) </v>`
    // (line 24) records whether AddEmptyLists instantiated the `#KRewrite` at lub(Int, Int)
    // and wrapped the whole rewrite in one IntList singleton, as the reference does, or
    // wrapped each side separately. Lines 21 and 27 are the variable and list-side controls.
    let oracle: ParametricIdOracle = toml::from_str(include_str!(
        "fixtures/reference/kompile/rewrite-list-singleton/reference.toml"
    ))
    .expect("reference id oracle should parse");
    let actual = fixture_rule_ids(
        "rewrite-list-singleton.k",
        include_str!("fixtures/reference/kompile/rewrite-list-singleton/test.k"),
        "REWRITE-LIST-SINGLETON",
    );
    let expected = oracle
        .rule
        .into_iter()
        .map(|rule| (rule.line, rule.unique_id))
        .collect::<BTreeMap<_, _>>();

    assert_eq!(actual, expected);
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct ConfigVarCastOracle {
    initializer: Vec<InitializerId>,
    cell: Vec<CellSymbolSorts>,
    config_var: Vec<ConfigVarSort>,
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct InitializerId {
    file: String,
    label: String,
    unique_id: String,
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct CellSymbolSorts {
    file: String,
    symbol: String,
    argument_sorts: Vec<String>,
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct ConfigVarSort {
    file: String,
    name: String,
    sort: String,
}

/// Compile a reference fixture through the whole kompile pipeline.
#[cfg(feature = "z3-inference")]
fn compile_fixture(
    file_name: &str,
    source: &str,
    main_module: &str,
) -> k_rust::kompile::CompiledKoreArtifacts {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(file_name, source),
        main_module,
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
    compile_loaded_definition(&loaded, CompileOptions::default())
        .expect("reference fixture should compile")
}

/// UNIQUE_ID of every generated cell-initializer axiom of an emitted definition.kore, keyed by
/// the initializer label (`initKCell`). Each axiom is written as one `  axiom` block whose first
/// `Lblinit...Cell{}(` occurrence is the initializer being defined.
#[cfg(feature = "z3-inference")]
fn initializer_ids(definition_kore: &str) -> BTreeMap<String, String> {
    definition_kore
        .split("\n  axiom")
        .skip(1)
        .filter_map(|axiom| {
            let start = axiom.find("Lblinit")?;
            let label = &axiom[start + "Lbl".len()..];
            let label = &label[..label.find('{')?];
            let id = axiom.split("UNIQUE'Unds'ID{}(\"").nth(1)?;
            let id = &id[..id.find('"')?];
            Some((label.to_owned(), id.to_owned()))
        })
        .collect()
}

/// The argument sorts of a cell symbol declaration (`symbol Lbl'-LT-'p'-GT-'{}(SortK{}) : ...`).
#[cfg(feature = "z3-inference")]
fn cell_symbol_argument_sorts(definition_kore: &str, symbol: &str) -> Option<Vec<String>> {
    let declaration = format!("symbol {symbol}{{}}(");
    let arguments = definition_kore
        .lines()
        .find_map(|line| line.trim_start().strip_prefix(&declaration))?;
    let arguments = &arguments[..arguments.find(')')?];
    Some(
        arguments
            .split(',')
            .map(|sort| sort.trim().to_owned())
            .filter(|sort| !sort.is_empty())
            .collect(),
    )
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_config_var_cast_initializer_ids_match() {
    // reference: k/result/bin/kompile --backend haskell --main-module CONFIG-VAR-CAST --syntax-module CONFIG-VAR-CAST test.k
    //   and --main-module CONFIG-VAR-INT --syntax-module CONFIG-VAR-INT test-bare-cell.k
    //
    // The mutable-bytes/default regression: the
    // reference's inference wraps a bare configuration variable in #SemanticCastTo<inferred
    // sort> (a KConfigVar constant is a variable, TypeInferenceVisitor.java:221-233), so
    // GenerateSentencesFromConfigDecl.getLeafInitializer hashes
    // `initKCell(Init) => <k> #SemanticCastToK(project:KItem(Init[$PGM])) </k>` and a bare
    // `<p> $P </p>` cell takes content sort K from that cast. initNCell (`$N:Int`) and the
    // literal initMCell are the controls; configVars.sh keeps declaring bare variables at KItem.
    let oracle: ConfigVarCastOracle = toml::from_str(include_str!(
        "fixtures/reference/kompile/config-var-cast/reference.toml"
    ))
    .expect("reference oracle should parse");
    let fixtures = [
        (
            "test.k",
            include_str!("fixtures/reference/kompile/config-var-cast/test.k"),
            "CONFIG-VAR-CAST",
        ),
        (
            "test-bare-cell.k",
            include_str!("fixtures/reference/kompile/config-var-cast/test-bare-cell.k"),
            "CONFIG-VAR-INT",
        ),
    ];
    for (file_name, source, main_module) in fixtures {
        let artifacts = compile_fixture(file_name, source, main_module);
        let actual = initializer_ids(&artifacts.definition_kore);
        let expected = oracle
            .initializer
            .iter()
            .filter(|row| row.file == file_name)
            .map(|row| (row.label.clone(), row.unique_id.clone()))
            .collect::<BTreeMap<_, _>>();
        assert!(!expected.is_empty(), "{file_name} has oracle rows");
        for (label, unique_id) in &expected {
            assert_eq!(
                actual.get(label),
                Some(unique_id),
                "{file_name}: UNIQUE_ID of {label} (all initializers: {actual:?})"
            );
        }
        for row in oracle.cell.iter().filter(|row| row.file == file_name) {
            assert_eq!(
                cell_symbol_argument_sorts(&artifacts.definition_kore, &row.symbol).as_ref(),
                Some(&row.argument_sorts),
                "{file_name}: argument sorts of {}",
                row.symbol
            );
        }
        let expected_config_vars = oracle
            .config_var
            .iter()
            .filter(|row| row.file == file_name)
            .map(|row| (row.name.clone(), Sort::new(&row.sort)))
            .collect::<BTreeMap<_, _>>();
        if !expected_config_vars.is_empty() {
            assert_eq!(
                artifacts.configuration_variables, expected_config_vars,
                "{file_name}: declared configuration variable sorts"
            );
        }
    }
}

#[cfg(feature = "z3-inference")]
#[derive(Deserialize)]
struct LambdaSortOracle {
    lambda: Vec<LambdaSignature>,
}

#[cfg(feature = "z3-inference")]
#[derive(Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd)]
struct LambdaSignature {
    line: usize,
    arguments: Vec<String>,
    total: bool,
}

#[cfg(feature = "z3-inference")]
#[test]
fn reference_let_list_binder_lambda_parameter_sorts_match() {
    // reference: k/result/bin/kompile --backend haskell --main-module LET-LIST-BINDER --syntax-module LET-LIST-BINDER test.k
    //
    // The WASM inferred-list-binder regression: the
    // generated `#lambda` production of a `#let`/`#fun` binder must take the same argument
    // sorts as the reference for a binder whose sort is only known by inference, including the
    // wasm-data/sparse-bytes.k:82-84 shape where the bound variable is a user-list element
    // (line 12, reference `(Chunks, Chunks, Int)`, not total), and the explicit-cast control
    // (line 21) must keep today's output.
    let source = include_str!("fixtures/reference/kompile/let-list-binder/test.k");
    let oracle: LambdaSortOracle = toml::from_str(include_str!(
        "fixtures/reference/kompile/let-list-binder/reference.toml"
    ))
    .expect("reference lambda oracle should parse");
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("let-list-binder.k", source),
        "LET-LIST-BINDER",
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
    let sentences = definition
        .modules
        .iter()
        .flat_map(|module| &module.sentences)
        .collect::<Vec<_>>();

    let attribute = |attributes: &k_rust::kore::ast::Attributes, name: &str| {
        attributes.0.iter().find_map(|attribute| match attribute {
            KorePattern::Application { symbol, arguments } if symbol.name == name => {
                match arguments.as_slice() {
                    [KorePattern::String(value)] => Some(value.clone()),
                    [] => Some(String::new()),
                    _ => None,
                }
            }
            _ => None,
        })
    };
    // Attribute each generated `#lambda` symbol to the source line of the rule that calls it:
    // the call-site axiom carries the rule's Location in both frontends, whereas only the
    // reference copies the local-function expression's Location onto the generated rule.
    let lambda_lines = sentences
        .iter()
        .filter_map(|sentence| {
            let KoreSentence::Axiom {
                pattern,
                attributes,
                ..
            } = sentence
            else {
                return None;
            };
            let line = attribute(
                attributes,
                "org'Stop'kframework'Stop'attributes'Stop'Location",
            )?
            .strip_prefix("Location(")?
            .split(',')
            .next()?
            .parse::<usize>()
            .ok()?;
            Some((format!("{pattern:?}"), line))
        })
        .fold(
            BTreeMap::<String, usize>::new(),
            |mut lines, (rendered, line)| {
                for (start, _) in rendered.match_indices("\"Lbl'Hash'lambda") {
                    let name = rendered[start + 1..]
                        .split('"')
                        .next()
                        .expect("a rendered symbol name closes its quote");
                    let entry = lines.entry(name.to_owned()).or_insert(line);
                    *entry = (*entry).min(line);
                }
                lines
            },
        );
    let actual = sentences
        .iter()
        .filter_map(|sentence| {
            let KoreSentence::SymbolDeclaration {
                symbol,
                argument_sorts,
                attributes,
                ..
            } = sentence
            else {
                return None;
            };
            let line = *lambda_lines.get(&symbol.name)?;
            let arguments = argument_sorts
                .iter()
                .map(|sort| match sort {
                    k_rust::kore::ast::Sort::Application { name, .. } => {
                        name.strip_prefix("Sort").unwrap_or(name).to_owned()
                    }
                    k_rust::kore::ast::Sort::Variable(name) => name.clone(),
                })
                .collect();
            Some(LambdaSignature {
                line,
                arguments,
                total: attribute(attributes, "total").is_some(),
            })
        })
        .collect::<BTreeSet<_>>();
    let expected = oracle.lambda.into_iter().collect::<BTreeSet<_>>();

    assert_eq!(
        actual, expected,
        "generated #lambda productions (line, argument sorts, total) differ from the reference"
    );
}

fn snapshot_attributes(attributes: &Attributes) -> BTreeMap<String, Value> {
    attributes
        .entries()
        .iter()
        .filter(|(key, _)| {
            !matches!(
                key.as_str(),
                "contentStartOffset"
                    | "org.kframework.attributes.SourceId"
                    | ORIGIN_ATTRIBUTE
                    | SENTENCE_START_OFFSET_ATTRIBUTE
                    | SENTENCE_END_OFFSET_ATTRIBUTE
            )
        })
        .map(|(key, value)| (key.clone(), value.clone()))
        .collect()
}

fn assert_generated_by(definition: &Definition, pass: GeneratingPass) {
    let receipts = definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| sentence.attributes().get(ORIGIN_ATTRIBUTE))
        .collect::<Vec<_>>();
    assert!(!receipts.is_empty(), "{pass:?} produced no receipts");
    assert!(
        receipts
            .iter()
            .all(|receipt| receipt["pass"] == pass.as_str()),
        "{receipts:#?}",
    );
}

fn assert_has_generated_by(definition: &Definition, pass: GeneratingPass) {
    assert!(
        definition
            .modules
            .iter()
            .flat_map(|module| &module.local_sentences)
            .filter_map(|sentence| sentence.attributes().get(ORIGIN_ATTRIBUTE))
            .any(|receipt| receipt["pass"] == pass.as_str()),
        "{pass:?} produced no receipts",
    );
}

#[test]
fn duplicates_commutative_simplification_rules_and_removes_rule_comm() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= Exp "+" Exp [comm, function, symbol(_+_)]
          rule X:Exp + Y:Exp => Y:Exp + X:Exp [simplification, comm, label(commute)]
        endmodule
    "#};
    let definition = resolve_comm(&parsed(source)).unwrap();
    let printer = Printer::new();
    let rules = definition.modules[0]
        .local_sentences
        .iter()
        .filter_map(|sentence| {
            let Sentence::Rule {
                body, attributes, ..
            } = sentence
            else {
                return None;
            };
            Some((printer.print_term(body), snapshot_attributes(attributes)))
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
}

#[test]
fn commutative_rule_copies_carry_their_source_rule_origin() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= Exp "+" Exp [comm, function, symbol(_+_)]
          rule X:Exp + Y:Exp => Y:Exp + X:Exp [simplification, comm, label(commute)]
        endmodule
    "#};
    let rule_text = "X:Exp + Y:Exp => Y:Exp + X:Exp";
    let start = source.find(rule_text).unwrap();
    let source_link = ProvenanceLink::Source {
        span: TermSpan {
            source: SourceId(0),
            start,
            end: start + rule_text.len(),
        },
    };
    let definition = resolve_comm(&parsed(source)).unwrap();
    let rules = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| matches!(sentence, Sentence::Rule { .. }))
        .collect::<Vec<_>>();

    assert_eq!(rules.len(), 2);
    for (sentence_index, sentence) in rules {
        let receipt = sentence.attributes().get(ORIGIN_ATTRIBUTE).unwrap();
        assert_eq!(receipt["pass"], GeneratingPass::ResolveComm.as_str());
        assert_eq!(
            receipt["destination"]["sentenceIndex"],
            serde_json::json!(sentence_index),
        );
        let Sentence::Rule { body, .. } = sentence else {
            unreachable!();
        };
        let origin = body
            .metadata()
            .and_then(|metadata| metadata.origin.as_deref())
            .expect("commutative rule body has an origin");
        assert_eq!(origin.pass, GeneratingPass::ResolveComm);
        assert!(origin.origins.contains(&source_link), "{origin:?}");
    }
}

#[test]
fn rejects_rule_comm_when_the_lhs_symbol_is_not_commutative() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= Exp "+" Exp [function, symbol(_+_)]
          rule X:Exp + Y:Exp => X:Exp [simplification, comm]
        endmodule
    "#};
    let error = resolve_comm(&parsed(source)).unwrap_err();

    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Used 'comm' attribute on simplification rule but _+_ is not comm."
    );
}

fn attributes(entries: &[(&str, Value)]) -> Attributes {
    Attributes::new(
        entries
            .iter()
            .map(|(key, value)| ((*key).into(), value.clone()))
            .collect::<BTreeMap<_, _>>(),
    )
}

fn application(label: &str, arguments: Vec<Term>) -> Term {
    Term::Apply {
        label: Label::new(label),
        arguments,
    }
}

fn rewrite(left: Term, right: Term) -> Term {
    Term::Rewrite {
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn truth() -> Term {
    Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    }
}

fn rule(body: Term, attributes: Attributes) -> Sentence {
    Sentence::Rule {
        body,
        requires: truth(),
        ensures: truth(),
        attributes,
    }
}

fn production(label: &str, sort: &str, attributes: Attributes) -> Sentence {
    Sentence::Production {
        label: Some(Label::new(label)),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: Vec::new(),
        attributes,
    }
}

fn module(name: &str, sentences: Vec<Sentence>) -> FlatModule {
    FlatModule {
        name: name.into(),
        imports: Vec::new(),
        local_sentences: sentences,
        attributes: Attributes::default(),
    }
}

fn incomplete_cell(label: &str, body: Term) -> Term {
    application(
        label,
        vec![
            application("#noDots", Vec::new()),
            body,
            application("#dots", Vec::new()),
        ],
    )
}

fn io_fixture(stream: &str) -> Definition {
    let builtin_init = rule(
        rewrite(
            application("initStdinCell", vec![Term::variable("Init")]),
            incomplete_cell(
                "<stdin>",
                application("builtinInput", vec![Term::variable("Init")]),
            ),
        ),
        attributes(&[("initializer", json!(""))]),
    );
    let unblock = rule(
        incomplete_cell(
            "<stdin>",
            rewrite(
                application(".List", Vec::new()),
                application(
                    "ListItem",
                    vec![application(
                        "#parseInput",
                        vec![
                            application("#SemanticCastToString", vec![Term::variable("?Sort")]),
                            application(
                                "#SemanticCastToString",
                                vec![Term::variable("?Delimiters")],
                            ),
                        ],
                    )],
                ),
            ),
        ),
        attributes(&[("label", json!("STDIN-STREAM.stdinUnblock"))]),
    );
    let stream_rule = rule(
        incomplete_cell("<stdin>", application("builtinStep", Vec::new())),
        attributes(&[("stream", json!(""))]),
    );
    let stdin = module(
        "STDIN-STREAM",
        vec![
            builtin_init,
            unblock,
            stream_rule,
            production("#buffer", "Stream", Attributes::default()),
        ],
    );

    let user_init = rule(
        rewrite(
            application("initInCell", vec![Term::variable("Init")]),
            incomplete_cell("<in>", application("oldInput", Vec::new())),
        ),
        attributes(&[("initializer", json!(""))]),
    );
    let consume = rule(
        incomplete_cell(
            "<in>",
            rewrite(
                application(
                    "ListItem",
                    vec![application(
                        "#SemanticCastToInt",
                        vec![Term::variable("Value")],
                    )],
                ),
                application(".List", Vec::new()),
            ),
        ),
        attributes(&[("label", json!("consume"))]),
    );
    let main = module(
        "MAIN",
        vec![
            production("<in>", "InCell", attributes(&[("stream", json!(stream))])),
            user_init,
            consume,
        ],
    );
    Definition {
        main_module: "MAIN".into(),
        modules: vec![
            main,
            stdin,
            module("STDOUT-STREAM", Vec::new()),
            module("K-IO", Vec::new()),
            module("K-REFLECTION", Vec::new()),
        ],
        attributes: Attributes::default(),
    }
}

#[test]
fn resolves_stream_initializers_unblocking_rules_and_builtin_sentences() {
    let mut input = io_fixture("stdin");
    input
        .modules
        .iter_mut()
        .find(|module| module.name == "K-IO")
        .unwrap()
        .local_sentences
        .push(production("ioHelper", "KItem", Attributes::default()));
    let resolved = ResolvedDefinition::resolve(&input).unwrap();
    let main_id = resolved.module_id("MAIN").unwrap();
    let catalog = resolved.production_catalog(main_id);
    let cell = catalog.productions_for(&LabelHead::from(&Label::new("<in>")))[0];
    let consume = input
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .iter_mut()
        .find(|sentence| sentence.attributes().get_str("label") == Some("consume"))
        .unwrap();
    let Sentence::Rule { body, .. } = consume else {
        unreachable!()
    };
    let taken = std::mem::replace(body, Term::Sequence(Vec::new()));
    *body = taken.with_metadata(TermMetadata {
        production: Some(ResolvedProductionId(cell.0)),
        ..TermMetadata::default()
    });

    let definition = resolve_io(&input).unwrap();
    let main = definition.main_module().unwrap();
    let rendered = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(main.imports.iter().any(|import| import.name == "K-IO"));
    assert!(
        main.imports
            .iter()
            .any(|import| import.name == "K-REFLECTION")
    );
    assert!(rendered.iter().any(|body| {
        body.contains("initInCell") && body.contains("builtinInput") && !body.contains("oldInput")
    }));
    assert!(rendered.iter().any(|body| {
        body.contains("#parseInput")
            && body.contains("#token(\"\\\"Int\\\"\",\"String\")")
            && body.contains("`<in>`")
    }));
    assert!(
        rendered
            .iter()
            .any(|body| body.contains("builtinStep") && body.contains("`<in>`"))
    );
    assert!(main.local_sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Production { sort, .. } if sort.name == "Stream")
    }));
    let generated_receipts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| sentence.attributes().get(ORIGIN_ATTRIBUTE))
        .collect::<Vec<_>>();
    assert!(!generated_receipts.is_empty());
    assert!(
        generated_receipts
            .iter()
            .all(|receipt| receipt["pass"] == GeneratingPass::ResolveIo.as_str())
    );
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let catalog = resolved.production_catalog(resolved.module_id("MAIN").unwrap());
    let consume = main
        .local_sentences
        .iter()
        .find(|sentence| sentence.attributes().get_str("label") == Some("consume"))
        .unwrap();
    let Sentence::Rule { body, .. } = consume else {
        unreachable!()
    };
    let rebased = body
        .metadata()
        .and_then(|metadata| metadata.production)
        .unwrap();
    assert!(matches!(
        catalog.production(ProductionId(rebased.0)),
        Sentence::Production { label: Some(label), .. } if label.name == "<in>"
    ));
    for template in ["STDIN-STREAM", "STDOUT-STREAM"] {
        let module = definition
            .modules
            .iter()
            .find(|module| module.name == template)
            .unwrap();
        assert!(module.imports.is_empty());
        assert!(module.local_sentences.is_empty());
    }
}

#[test]
fn stdin_unblocking_rejects_multiple_matches_and_generates_one_for_single_match() {
    let single = resolve_io(&io_fixture("stdin")).unwrap();
    let consume_rules = single
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("consume") => Some(body),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(consume_rules.len(), 2);
    assert_eq!(
        consume_rules
            .iter()
            .filter(|body| Printer::new().print_term(body).contains("#parseInput"))
            .count(),
        1
    );

    let mut multiple = io_fixture("stdin");
    let consume = multiple
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .iter_mut()
        .find(|sentence| sentence.attributes().get_str("label") == Some("consume"))
        .unwrap();
    let Sentence::Rule {
        body,
        attributes: rule_attributes,
        ..
    } = consume
    else {
        unreachable!()
    };
    *body = Term::Sequence(vec![body.clone(), body.clone()]);
    *rule_attributes = attributes(&[
        ("label", json!("consume")),
        ("org.kframework.attributes.Source", json!("wem14.k")),
        ("org.kframework.attributes.Location", json!([7, 3, 9, 20])),
    ]);

    let error = resolve_io(&multiple).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    let diagnostic = &error.diagnostics[0];
    assert_eq!(diagnostic.severity, k_rust::diagnostic::Severity::Error);
    assert_eq!(
        diagnostic.code,
        k_rust::diagnostic::DiagnosticCode::InvalidIoStream
    );
    assert_eq!(
        diagnostic.message,
        "A stdin rule may match the stream cell at most once."
    );
    assert_eq!(diagnostic.source.as_deref(), Some("wem14.k"));
    assert_eq!(
        diagnostic.location,
        Some(k_rust::definition::Location {
            start_line: 7,
            start_column: 3,
            end_line: 9,
            end_column: 20,
        })
    );
}

#[test]
fn rejects_unknown_stream_names() {
    let error = resolve_io(&io_fixture("stderr")).unwrap_err();

    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Make sure you give the correct stream names: stderr\nIt should be one of [stdin, stdout]"
    );
}

#[test]
fn lowers_local_functions_with_closure_arguments_and_totality() {
    let x = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Int")),
    };
    let y = Term::Variable {
        name: "Y".into(),
        sort: Some(Sort::new("Int")),
    };
    let local_function = application(
        "#fun3",
        vec![
            x.clone(),
            application("plus", vec![x, y.clone()]),
            Term::Token {
                token: "1".into(),
                sort: Sort::new("Int"),
            },
        ],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("plus")),
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    items: vec![
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Int"),
                            name: None,
                        },
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Int"),
                            name: None,
                        },
                    ],
                    attributes: Attributes::default(),
                },
                rule(local_function, Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    let lambda = sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } if label.name.starts_with("#lambda") => {
                Some((label.clone(), items.clone(), attributes.clone()))
            }
            _ => None,
        })
        .expect("lambda production should be generated");
    assert_eq!(lambda.0.name, "#lambda__");
    assert_eq!(
        lambda
            .1
            .iter()
            .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
            .count(),
        2,
        "the argument and captured Y should be explicit parameters"
    );
    assert!(lambda.2.get("function").is_some());
    assert!(lambda.2.get("total").is_some());

    let rendered = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered
            .iter()
            .any(|body| body.contains("`#lambda__`(#token(\"1\",\"Int\"),Y)")),
        "{rendered:#?}"
    );
    assert!(
        rendered
            .iter()
            .any(|body| { body.contains("`#lambda__`(X,Y)=>plus(X,Y)") })
    );
    let receipts = sentences
        .iter()
        .filter_map(|sentence| sentence.attributes().get(ORIGIN_ATTRIBUTE))
        .collect::<Vec<_>>();
    assert!(!receipts.is_empty());
    assert!(
        receipts
            .iter()
            .all(|receipt| receipt["pass"] == GeneratingPass::ResolveFun.as_str())
    );
}

#[test]
fn nested_local_functions_scope_closures_to_their_own_patterns() {
    let variable = |name: &str| Term::Variable {
        name: name.into(),
        sort: Some(Sort::new("K")),
    };
    let inner = application(
        "#fun2",
        vec![
            rewrite(
                variable("C"),
                Term::Sequence(vec![variable("A"), variable("B"), variable("C")]),
            ),
            variable("B"),
        ],
    );
    let outer = application("#fun2", vec![rewrite(variable("B"), inner), variable("A")]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module("MAIN", vec![rule(outer, Attributes::default())])],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    let lambda_arities = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if label.name.starts_with("#lambda") => Some(
                items
                    .iter()
                    .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                    .count(),
            ),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(lambda_arities, vec![2, 3]);

    for sentence in sentences {
        let Sentence::Rule { body, .. } = sentence else {
            continue;
        };
        let Term::Rewrite { left, right } = body.unannotated() else {
            continue;
        };
        let Term::Apply { label, .. } = left.unannotated() else {
            continue;
        };
        if !label.name.starts_with("#lambda") {
            continue;
        }
        let mut lhs = BTreeSet::new();
        left.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term {
                lhs.insert(name.clone());
            }
        });
        let mut rhs = BTreeSet::new();
        right.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term {
                rhs.insert(name.clone());
            }
        });
        assert!(
            rhs.is_subset(&lhs),
            "generated {label} rule has unbound RHS variables: {:?}",
            rhs.difference(&lhs).collect::<Vec<_>>()
        );
    }
}

#[test]
fn matching_patterns_bind_their_anonymous_variables_instead_of_closing_over_them() {
    // regression-new/equals-pattern: `rule baz(A:KItem) => #fun(baz(B) => baz(bar(_)) :=K
    // baz(B))(baz(A))`. K's ComputeUnboundVariables visits the left child of `:=K`/`:/=K` with
    // isInKLhs set, so nothing in a matching pattern is a closure variable: the reference
    // declares `#lambda_baz(_)_..._(KItem)` with one parameter and the rule
    // `#lambda_baz(baz(bar(_Gen0))) => true` binds the anonymous variable in its own pattern.
    let variable = |name: &str, sort: &str| Term::Variable {
        name: name.into(),
        sort: Some(Sort::new(sort)),
    };
    let anonymous = || Term::Variable {
        name: "_".into(),
        sort: None,
    };
    let baz = |argument: Term| application("baz", vec![argument]);
    let bar = |argument: Term| application("bar", vec![argument]);
    let matching = application(
        "_:=K_",
        vec![baz(bar(anonymous())), baz(variable("B", "KItem"))],
    );
    let local = application(
        "#fun2",
        vec![
            rewrite(baz(variable("B", "KItem")), matching),
            baz(variable("A", "KItem")),
        ],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("KItem"),
                    attributes: Attributes::default(),
                },
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("baz")),
                    parameters: Vec::new(),
                    sort: Sort::new("KItem"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: Sort::new("KItem"),
                        name: None,
                    }],
                    attributes: Attributes::default(),
                },
                Sentence::Production {
                    label: Some(Label::new("bar")),
                    parameters: Vec::new(),
                    sort: Sort::new("KItem"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Int"),
                        name: None,
                    }],
                    attributes: Attributes::default(),
                },
                rule(
                    rewrite(baz(variable("A", "KItem")), local),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    let lambda_arities = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if label.name.starts_with("#lambda") => Some((
                label.name.clone(),
                items
                    .iter()
                    .filter(|item| matches!(item, ProductionItem::NonTerminal { .. }))
                    .count(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        lambda_arities
            .iter()
            .map(|(_, arity)| *arity)
            .collect::<Vec<_>>(),
        vec![1, 1],
        "neither the local function nor the matching predicate closes over the anonymous variable: {lambda_arities:?}"
    );

    let mut generated_rules = 0;
    for sentence in sentences {
        let Sentence::Rule { body, .. } = sentence else {
            continue;
        };
        let Term::Rewrite { left, right } = body.unannotated() else {
            continue;
        };
        let Term::Apply { label, arguments } = left.unannotated() else {
            continue;
        };
        if !label.name.starts_with("#lambda") {
            // The original rule calls the local function with its argument alone.
            let Term::Apply {
                label: call,
                arguments: call_arguments,
            } = right.unannotated()
            else {
                panic!("the rule's RHS is the local-function call");
            };
            assert!(call.name.starts_with("#lambda"), "{}", call.name);
            assert_eq!(
                call_arguments.len(),
                1,
                "{}",
                Printer::new().print_term(body)
            );
            continue;
        }
        generated_rules += 1;
        assert_eq!(arguments.len(), 1, "{}", Printer::new().print_term(body));
        let mut lhs = BTreeSet::new();
        left.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term {
                assert_ne!(name, "_", "{}", Printer::new().print_term(body));
                lhs.insert(name.clone());
            }
        });
        let mut rhs = BTreeSet::new();
        right.visit_preorder(&mut |term| {
            if let Term::Variable { name, .. } = term {
                rhs.insert(name.clone());
            }
        });
        assert!(
            rhs.is_subset(&lhs),
            "generated {label} rule has unbound RHS variables: {:?}",
            rhs.difference(&lhs).collect::<Vec<_>>()
        );
    }
    assert_eq!(
        generated_rules, 3,
        "outer lambda rule, matching rule, owise rule"
    );
}

#[test]
fn local_function_variable_patterns_keep_the_k_parameter_sort() {
    let b = Sort::new("B");
    let local_function = application(
        "#let",
        vec![
            Term::variable("X"),
            Term::Token {
                token: "b".into(),
                sort: b.clone(),
            },
            Term::variable("X"),
        ],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: b.clone(),
                    attributes: Attributes::default(),
                },
                rule(local_function, Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = resolve_fun(&definition).unwrap();
    let argument_sort = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if label.name.starts_with("#lambda") => items.iter().find_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            }),
            _ => None,
        })
        .unwrap();

    assert_eq!(argument_sort, &Sort::new("K"));

    let injected = add_sort_injections_to_definition(&transformed).unwrap();
    for sentence in injected.main_module().unwrap().local_sentences.iter() {
        let Sentence::Rule { body, .. } = sentence else {
            continue;
        };
        body.visit_preorder(&mut |term| {
            let Term::Apply { label, .. } = term else {
                return;
            };
            if label.name == "inj"
                && label
                    .parameters
                    .first()
                    .is_some_and(|sort| sort.name == "K")
                && label.parameters.get(1).is_some_and(|sort| sort.name == "B")
            {
                panic!("lambda lowering emitted an impossible K-to-B downcast: {term:?}");
            }
        });
    }
}

#[test]
fn local_function_singleton_user_list_arguments_keep_the_k_parameter_sort() {
    let item = Sort::new("Item");
    let items = Sort::new("Items");
    let local_function = application(
        "#let",
        vec![
            Term::Variable {
                name: "X".into(),
                sort: Some(item),
            },
            Term::Token {
                token: "items".into(),
                sort: items.clone(),
            },
            Term::variable("X"),
        ],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: items.clone(),
                    attributes: Attributes::default(),
                },
                production(".Items", "Items", attributes(&[("userList", json!(""))])),
                rule(local_function, Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = resolve_fun(&definition).unwrap();
    let (argument_sort, lambda_attributes) = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                attributes,
                ..
            } if label.name.starts_with("#lambda") => Some((
                items.iter().find_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort),
                    _ => None,
                })?,
                attributes,
            )),
            _ => None,
        })
        .unwrap();

    assert_eq!(
        argument_sort,
        &Sort::new("K"),
        "an uncast variable pattern contributes K even for a user-list argument"
    );
    assert!(lambda_attributes.get("total").is_some());
}

#[test]
fn gives_generated_lambdas_definition_wide_unique_labels() {
    let local_function = || {
        application(
            "#fun3",
            vec![
                Term::variable("X"),
                Term::variable("X"),
                Term::Token {
                    token: "1".into(),
                    sort: Sort::new("Int"),
                },
            ],
        )
    };
    let syntax = || Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Int"),
        attributes: Attributes::default(),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module(
                "LIB",
                vec![syntax(), rule(local_function(), Attributes::default())],
            ),
            FlatModule {
                name: "MAIN".into(),
                imports: vec![FlatImport {
                    name: "LIB".into(),
                    public: true,
                }],
                local_sentences: vec![syntax(), rule(local_function(), Attributes::default())],
                attributes: Attributes::default(),
            },
        ],
        attributes: Attributes::default(),
    };

    let transformed = resolve_fun(&definition).unwrap();
    let labels = transformed
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } if label.name.starts_with("#lambda") => Some(label.name.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(labels, ["#lambda__", "#lambda__2"]);
    add_sort_injections_to_definition(&transformed)
        .expect("generated lambda calls should remain unambiguous across imports");
}

#[test]
fn lowers_k_non_matching_to_a_negated_predicate_with_owise_rule() {
    let pattern = rewrite(
        Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("Int")),
        },
        bool_token_for_test(true),
    );
    let expression = Term::Token {
        token: "0".into(),
        sort: Sort::new("Int"),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: Attributes::default(),
                },
                rule(
                    application("_:/=K_", vec![pattern, expression]),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    assert!(sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Rule { attributes, .. } if attributes.get("owise").is_some())
    }));
    let rendered = sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered
            .iter()
            .any(|body| { body.contains("`notBool_`(`#lambda") }),
        "{rendered:#?}"
    );
}

fn bool_token_for_test(value: bool) -> Term {
    Term::Token {
        token: value.to_string(),
        sort: Sort::new("Bool"),
    }
}

#[test]
fn rebases_parser_metadata_after_generating_lambda_productions() {
    let source = indoc! {r##"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "f(" Int ")" [function, symbol(f)]
          syntax Int ::= "#fun" "(" Int "=>" Int ")" "(" Int ")" [symbol(#fun3)]
          rule f(X:Int) => #fun(Y:Int => Y:Int)(X:Int)
        endmodule
    "##};
    let transformed = resolve_fun(&parsed(source)).unwrap();

    module_to_kore(&transformed, "MAIN")
        .expect("surviving parser production metadata should use the expanded catalog");
}

#[test]
fn threads_configuration_through_transitive_function_calls() {
    let function = attributes(&[("function", json!(""))]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("reader", "Int", function.clone()),
                production("caller", "Int", function),
                production("plain", "Int", Attributes::default()),
                rule(
                    rewrite(
                        application("reader", Vec::new()),
                        Term::Variable {
                            name: "!Fresh".into(),
                            sort: Some(Sort::new("Int")),
                        },
                    ),
                    Attributes::default(),
                ),
                rule(
                    rewrite(
                        application("caller", Vec::new()),
                        application("reader", Vec::new()),
                    ),
                    Attributes::default(),
                ),
                rule(
                    rewrite(
                        application("plain", Vec::new()),
                        application("caller", Vec::new()),
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_function_with_config(&definition).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        main.local_sentences.iter().any(|sentence| matches!(
            sentence,
            Sentence::SyntaxSort { sort, .. } if sort == &Sort::new("GeneratedTopCell")
        )),
        "adding configuration arguments must also declare GeneratedTopCell"
    );
    let production_arities = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } => Some((label.name.as_str(), items.len())),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(production_arities["reader"], 1);
    assert_eq!(production_arities["caller"], 1);
    assert_eq!(production_arities["plain"], 0);

    let rendered = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered
            .iter()
            .any(|body| body.contains("caller(#Configuration)=>reader(#Configuration)")),
        "{rendered:#?}"
    );
    assert!(
        rendered
            .iter()
            .any(|body| body == "plain(.KList)=>caller(#Configuration)"),
        "{rendered:#?}"
    );
    let receipts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| sentence.attributes().get(ORIGIN_ATTRIBUTE))
        .collect::<Vec<_>>();
    assert!(!receipts.is_empty());
    assert!(
        receipts.iter().all(|receipt| {
            receipt["pass"] == GeneratingPass::ResolveFunctionWithConfig.as_str()
        })
    );
}

#[test]
fn function_dependencies_ignore_anywhere_macro_classification() {
    for macro_kind in [
        None,
        Some("macro"),
        Some("macro-rec"),
        Some("alias"),
        Some("alias-rec"),
    ] {
        let function = attributes(&[("function", json!(""))]);
        let mut helper_attributes = attributes(&[("anywhere", json!(""))]);
        if let Some(macro_kind) = macro_kind {
            helper_attributes.insert(macro_kind, json!(""));
        }
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module(
                "MAIN",
                vec![
                    production("reader", "Int", function.clone()),
                    production("helper", "Int", function.clone()),
                    production("caller", "Int", function),
                    rule(
                        rewrite(
                            application("reader", Vec::new()),
                            Term::Variable {
                                name: "!Fresh".into(),
                                sort: Some(Sort::new("Int")),
                            },
                        ),
                        Attributes::default(),
                    ),
                    rule(
                        rewrite(
                            application("helper", Vec::new()),
                            application("reader", Vec::new()),
                        ),
                        helper_attributes,
                    ),
                    rule(
                        rewrite(
                            application("caller", Vec::new()),
                            application("helper", Vec::new()),
                        ),
                        Attributes::default(),
                    ),
                ],
            )],
            attributes: Attributes::default(),
        };

        let transformed = resolve_function_with_config(&definition).unwrap();
        let arities = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Production {
                    label: Some(label),
                    items,
                    ..
                } => Some((label.name.as_str(), items.len())),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(arities["reader"], 1, "{macro_kind:?}");
        assert_eq!(arities["helper"], 1, "{macro_kind:?}");
        assert_eq!(arities["caller"], 1, "{macro_kind:?}");
    }
}

#[test]
fn lowers_with_config_rules_to_a_top_cell_alias() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("f", "Int", attributes(&[("function", json!(""))])),
                rule(
                    application(
                        "#withConfig",
                        vec![
                            rewrite(application("f", Vec::new()), truth()),
                            incomplete_cell("<k>", Term::variable("K")),
                        ],
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_function_with_config(&definition).unwrap();
    let rendered = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();
    assert!(rendered.starts_with("f(`<generatedTop>`("), "{rendered}");
    assert!(rendered.contains("#dots(.KList),"), "{rendered}");
    assert!(rendered.contains(" #as #Configuration"), "{rendered}");
    assert!(rendered.contains("#Configuration"), "{rendered}");
    assert!(
        rendered.ends_with(")=>#token(\"true\",\"Bool\")"),
        "{rendered}"
    );
}

#[test]
fn rebases_function_metadata_after_adding_configuration_arguments() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "f(" Int ")" [function, symbol(f)]
          rule f(X:Int) => !Y:Int
        endmodule
    "#};
    let transformed = resolve_function_with_config(&parsed(source)).unwrap();
    let resolved = ResolvedDefinition::resolve(&transformed).unwrap();
    let module = resolved.module_id("MAIN").unwrap();
    let productions = resolved.production_catalog(module);
    let rule = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let Term::Rewrite { left, .. } = rule.unannotated() else {
        panic!("parsed rule should contain a rewrite")
    };
    let Term::Apply { label, arguments } = left.unannotated() else {
        panic!("parsed rule lhs should be an application")
    };
    assert_eq!(label.name, "f");
    assert_eq!(arguments.len(), 2);
    let production = left
        .metadata()
        .and_then(|metadata| metadata.production)
        .map(|id| productions.production(k_rust::definition::ProductionId(id.0)))
        .expect("parsed application should retain transformed production identity");
    assert!(matches!(
        production,
        Sentence::Production { items, .. }
            if matches!(items.last(), Some(ProductionItem::NonTerminal { sort, .. })
                if sort.name == "GeneratedTopCell")
    ));
}

#[test]
fn aliases_a_rewritten_top_cell_when_configuration_is_used() {
    let top = application(
        "<generatedTop>",
        vec![application("<k>", vec![Term::variable("K")])],
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::Rule {
                body: rewrite(top.clone(), top),
                requires: application("needs", vec![Term::variable("#Configuration")]),
                ensures: truth(),
                attributes: Attributes::default(),
            }],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_config_var(&definition);
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let Term::Rewrite { left, .. } = body.unannotated() else {
        panic!("configuration rule should remain a rewrite")
    };
    assert!(matches!(left.unannotated(), Term::As { alias, .. }
        if matches!(alias.unannotated(), Term::Variable { name, .. }
            if name == "#Configuration")));
    let origin = left
        .metadata()
        .and_then(|metadata| metadata.origin.as_deref())
        .expect("the generated configuration alias should have an origin");
    assert_eq!(origin.pass, GeneratingPass::ResolveFunctionWithConfig);
    assert_eq!(origin.destination.as_ref().unwrap().path, [0, 0]);
}

#[test]
fn does_not_alias_a_top_cell_for_unresolved_fresh_variables_alone() {
    let top = application(
        "<generatedTop>",
        vec![application("<k>", vec![Term::variable("K")])],
    );
    let original = rewrite(top.clone(), top);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::Rule {
                body: original.clone(),
                requires: application("needs", vec![Term::variable("!Fresh")]),
                ensures: truth(),
                attributes: Attributes::default(),
            }],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_config_var(&definition);
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert_eq!(body, &original);
}

#[test]
fn assigns_stable_alpha_normalized_sentence_ids() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "f(" Exp ")" [symbol(f)]
          rule f(X:Exp) => X:Exp [label(first)]
          rule f(Y:Exp) => Y:Exp [label(second)]
          rule f(Z:Exp) => Z:Exp [owise, label(otherwise)]
        endmodule
    "#};
    let transformed = number_sentences(&parsed(source));
    let ids = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { attributes, .. } => Some((
                attributes.get_str("label").map(str::to_owned),
                attributes
                    .get_str("UNIQUE_ID")
                    .expect("rules are numbered")
                    .to_owned(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    assert_eq!(ids[0].1, ids[1].1);
    assert_ne!(ids[0].1, ids[2].1);
    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(ids);
    });
}

#[test]
fn preserves_existing_sentence_ids() {
    let mut attributes = Attributes::default();
    attributes.insert("UNIQUE_ID", json!("already-numbered"));
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                rewrite(application("f", Vec::new()), truth()),
                attributes,
            )],
        )],
        attributes: Attributes::default(),
    };
    let transformed = number_sentences(&definition);
    assert_eq!(
        transformed.main_module().unwrap().local_sentences[0]
            .attributes()
            .get_str("UNIQUE_ID"),
        Some("already-numbered")
    );
}

#[test]
fn lowers_heat_and_cool_attributes_to_result_predicates() {
    let source = indoc! {r#"
        module MAIN
          syntax KResult
          syntax Exp ::= "heat" [symbol(heat)]
                       | "cool" [symbol(cool)]
          rule heat => cool [heat, result(KResult)]
          rule cool => heat [cool, result(KResult)]
        endmodule
    "#};
    let transformed = resolve_heat_cool_attributes(&parsed(source)).unwrap();
    let requires = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { requires, .. } => Some(Printer::new().print_term(requires)),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(requires);
    });
    assert_generated_by(&transformed, GeneratingPass::ResolveHeatCool);
}

#[test]
fn heat_cool_ignores_non_rule_sentence_kinds_before_predicate_lookup() {
    for kind in ["heat", "cool"] {
        let attrs = attributes(&[(kind, json!("")), ("result", json!("Missing"))]);
        let sentences = vec![
            production("a", "Exp", attrs.clone()),
            Sentence::Claim {
                body: rewrite(application("a", Vec::new()), application("a", Vec::new())),
                requires: truth(),
                ensures: truth(),
                attributes: attrs.clone(),
            },
            Sentence::ContextAlias {
                body: Term::variable("HOLE"),
                requires: truth(),
                attributes: attrs,
            },
        ];
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module("MAIN", sentences.clone())],
            attributes: Attributes::default(),
        };
        let transformed = resolve_heat_cool_attributes(&definition)
            .expect("ignored sentence kinds must not require a strictness predicate");
        assert_eq!(
            transformed.main_module().unwrap().local_sentences,
            sentences
        );
    }
}

#[test]
fn heat_cool_still_rejects_rules_and_contexts_without_result_predicates() {
    for kind in ["heat", "cool"] {
        let attrs = attributes(&[(kind, json!("")), ("result", json!("Missing"))]);
        for sentence in [
            rule(
                rewrite(application("a", Vec::new()), truth()),
                attrs.clone(),
            ),
            Sentence::Context {
                body: Term::variable("HOLE"),
                requires: truth(),
                attributes: attrs,
            },
        ] {
            let definition = Definition {
                main_module: "MAIN".into(),
                modules: vec![module("MAIN", vec![sentence])],
                attributes: Attributes::default(),
            };
            let error = resolve_heat_cool_attributes(&definition).unwrap_err();
            assert_eq!(error.diagnostics.len(), 1);
            assert_eq!(
                error.diagnostics[0].code,
                k_rust::diagnostic::DiagnosticCode::InvalidHeatCool
            );
            assert!(
                error.diagnostics[0].message.starts_with(
                    "Definition is missing function isMissing required for strictness."
                )
            );
        }
    }
}

#[test]
fn removes_semantic_casts_and_retains_inferred_variable_sorts() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [symbol(f)]
          rule f(X:Exp) => X:Exp
        endmodule
    "#};
    let transformed = resolve_semantic_casts(&parsed(source));
    let rule = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let mut variables = Vec::new();
    rule.visit_preorder(&mut |term| {
        if let Term::Variable { name, sort } = term {
            variables.push((name.clone(), sort.clone()));
        }
    });
    let output = (Printer::new().print_term(rule), variables);

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_generated_by(&transformed, GeneratingPass::SemanticCasts);
}

#[test]
fn semantic_cast_sort_metadata_disambiguates_manually_built_applications() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("choice", "A", Attributes::default()),
                production("choice", "B", Attributes::default()),
                rule(
                    application("#SemanticCastToA", vec![application("choice", Vec::new())]),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = resolve_semantic_casts(&definition);
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        body.metadata().and_then(|metadata| metadata.sort.as_ref()),
        Some(&Sort::new("A"))
    );
}

#[test]
fn adds_kitem_subsorts_for_every_non_parser_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
          syntax Data ::= "d" [symbol(d)]
          syntax #Internal ::= "internal" [symbol(internal)]
          rule a => d
        endmodule
    "#};
    let transformed = subsort_kitem(&parsed(source)).unwrap();
    let generated = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: None,
                sort,
                items,
                attributes,
                ..
            } if sort == &Sort::new("KItem") && attributes.is_empty() => match items.as_slice() {
                [ProductionItem::NonTerminal { sort: child, .. }] => {
                    Some((sort.to_string(), child.to_string()))
                }
                _ => None,
            },
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(generated);
    });
    assert_generated_by(&transformed, GeneratingPass::SubsortKItem);
}

#[test]
fn folds_pure_constants_only_on_rule_right_hand_sides_and_conditions() {
    let source = indoc! {r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Bool [hook(BOOL.Bool)]
          syntax Int ::= r"[\\+\\-]?[0-9]+" [token, prec(2)]
          syntax Bool ::= r"true|false" [token]
          syntax Int ::= "add(" Int "," Int ")" [function, hook(INT.add), symbol(add)]
          syntax Bool ::= "eq(" Int "," Int ")" [function, hook(INT.eq), symbol(eq)]
          rule add(1, 2) => add(add(1, 2), 39)
            requires eq(add(1, 1), 2)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = constant_fold(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, requires, .. } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
            )),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_generated_by(&transformed, GeneratingPass::ConstantFolding);
}

#[test]
fn folds_integer_parameters_only_through_the_reference_unsigned_bound() {
    let control =
        include_str!("fixtures/reference/kompile/constant-folding-integer-bounds/control.k");
    let folded_right = |source: &str| {
        let transformed = constant_fold(&resolve_semantic_casts(&parsed(source))).unwrap();
        transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule { body, .. } => match body.unannotated() {
                    Term::Rewrite { right, .. } => Some(right.unannotated().clone()),
                    _ => None,
                },
                _ => None,
            })
            .unwrap()
    };
    assert_eq!(
        folded_right(control),
        Term::Token {
            token: "0".into(),
            sort: Sort::new("Int"),
        }
    );
    assert_eq!(
        folded_right(&control.replace("0 >>Int 2147483647", "8 >>Int 1")),
        Term::Token {
            token: "4".into(),
            sort: Sort::new("Int"),
        }
    );

    let negative =
        include_str!("fixtures/reference/kompile/constant-folding-integer-bounds/test.k");
    for value in ["-1", "2147483648", "4294967295", "4294967296"] {
        let source = negative.replace("2147483648", value);
        let error = constant_fold(&resolve_semantic_casts(&parsed(&source))).unwrap_err();
        assert_eq!(error.diagnostics.len(), 1, "bound {value}");
        assert_eq!(
            error.diagnostics[0].message,
            "Argument to hook INT.shr out of range. Expected a 32-bit unsigned integer.",
            "bound {value}"
        );
    }
}

#[cfg(feature = "mpfr-folding")]
#[test]
fn folds_mpfr_float_constants_with_their_declared_contexts() {
    let source = indoc! {r#"
        module MAIN
          syntax Float [hook(FLOAT.Float)]
          syntax Int [hook(INT.Int)]
          syntax Float ::= r"([\\+\\-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+\\-]?[0-9]+)?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(1)]
          syntax Float ::= "add(" Float "," Float ")" [function, hook(FLOAT.add), symbol(addFloat)]
          syntax Int ::= "exponent(" Float ")" [function, hook(FLOAT.exponent), symbol(floatExponent)]
          syntax Float ::= "floatResult" [symbol(floatResult)]
          syntax Int ::= "intResult" [symbol(intResult)]

          rule floatResult => add(0.1, 0.2)
          rule floatResult => add(3.4028235e38p24x8, 3.4028235e38p24x8)
          rule intResult => exponent(1.40129846e-45p24x8)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = constant_fold(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn folds_unicode_string_hooks_with_java_token_wrapping() {
    let string_sort = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("String"),
        attributes: attributes(&[("hook", json!("STRING.String"))]),
    };
    let concat = Sentence::Production {
        label: Some(Label::new("concat")),
        parameters: Vec::new(),
        sort: Sort::new("String"),
        items: vec![
            ProductionItem::NonTerminal {
                sort: Sort::new("String"),
                name: None,
            },
            ProductionItem::NonTerminal {
                sort: Sort::new("String"),
                name: None,
            },
        ],
        attributes: attributes(&[("function", json!("")), ("hook", json!("STRING.concat"))]),
    };
    let token = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("String"),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                string_sort,
                concat,
                rule(
                    rewrite(
                        application("result", Vec::new()),
                        application("concat", vec![token("\"λ\""), token("\"🦀\"")]),
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let transformed = constant_fold(&definition).unwrap();
    let Sentence::Rule { body, .. } = &transformed.main_module().unwrap().local_sentences[2] else {
        unreachable!()
    };
    let Term::Rewrite { right, .. } = body.unannotated() else {
        unreachable!()
    };
    assert_eq!(
        right.unannotated(),
        &Term::Token {
            token: "\"\\u03bb\\U0001f980\"".into(),
            sort: Sort::new("String"),
        }
    );
}

#[test]
fn folds_string_chr_only_for_unicode_scalar_values() {
    // reference: pinned K folds D7FF, E000, and 10FFFF to valid KORE, but its D800 and DFFF
    // artifacts are rejected by both the Haskell backend and standalone kore-parser.
    let source = |value: &str| {
        format!(
            r#"
            module MAIN
              syntax Int [hook(INT.Int)]
              syntax String [hook(STRING.String)]
              syntax Int ::= r"[\\+\\-]?[0-9]+" [token]
              syntax String ::= "result" [function, symbol(result)]
              syntax String ::= "chr(" Int ")" [function, hook(STRING.chr), symbol(chr)]
              rule result => chr({value})
            endmodule
            "#
        )
    };
    let folded = |value: &str| {
        let transformed = constant_fold(&resolve_semantic_casts(&parsed(&source(value)))).unwrap();
        let right = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule { body, .. } => match body.unannotated() {
                    Term::Rewrite { right, .. } => Some(right.unannotated().clone()),
                    _ => None,
                },
                _ => None,
            })
            .unwrap();
        (transformed, right)
    };
    for (codepoint, token, scalar) in [
        ("55295", r#""\ud7ff""#, "\u{d7ff}"),
        ("57344", r#""\ue000""#, "\u{e000}"),
        ("1114111", r#""\U0010ffff""#, "\u{10ffff}"),
    ] {
        let (transformed, right) = folded(codepoint);
        assert_eq!(
            right,
            Term::Token {
                token: token.into(),
                sort: Sort::new("String"),
            }
        );
        let kore = term_to_kore(&transformed, "MAIN", &right).unwrap();
        let reparsed = k_rust::kore::parser::parse_pattern(&kore.to_string()).unwrap();
        assert!(matches!(
            reparsed,
            k_rust::kore::ast::Pattern::DomainValue { ref value, .. } if value == scalar
        ));
    }

    for codepoint in ["-1", "1114112"] {
        let error =
            constant_fold(&resolve_semantic_casts(&parsed(&source(codepoint)))).unwrap_err();
        assert_eq!(error.diagnostics.len(), 1, "code point {codepoint}");
        assert_eq!(
            error.diagnostics[0].message,
            "Argument to hook STRING.chr out of range. Expected a number between 0 and 1114111.",
            "code point {codepoint}"
        );
    }
    for codepoint in ["55296", "57343"] {
        let error =
            constant_fold(&resolve_semantic_casts(&parsed(&source(codepoint)))).unwrap_err();
        assert_eq!(error.diagnostics.len(), 1, "code point {codepoint}");
        assert_eq!(
            error.diagnostics[0].message,
            "Argument to hook STRING.chr is a surrogate code point. Expected a Unicode scalar value.",
            "code point {codepoint}"
        );
    }
}

#[test]
fn reports_invalid_constant_operations() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::SyntaxSort {
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    attributes: attributes(&[("hook", json!("INT.Int"))]),
                },
                Sentence::Production {
                    label: Some(Label::new("divide")),
                    parameters: Vec::new(),
                    sort: Sort::new("Int"),
                    items: vec![
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Int"),
                            name: None,
                        },
                        ProductionItem::NonTerminal {
                            sort: Sort::new("Int"),
                            name: None,
                        },
                    ],
                    attributes: attributes(&[("hook", json!("INT.tdiv"))]),
                },
                rule(
                    rewrite(
                        application("result", Vec::new()),
                        application(
                            "divide",
                            vec![
                                Term::Token {
                                    token: "1".into(),
                                    sort: Sort::new("Int"),
                                },
                                Term::Token {
                                    token: "0".into(),
                                    sort: Sort::new("Int"),
                                },
                            ],
                        ),
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let error = constant_fold(&definition).unwrap_err();
    assert_eq!(error.diagnostics[0].message, "Division by zero.");
}

#[test]
fn propagates_production_macro_kinds_except_to_simplification_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro-rec, symbol(m)]
          rule m(X:Exp) => X:Exp [label(expand)]
          rule m(a) => a [simplification, label(simplify)]
        endmodule
    "#};
    let transformed = propagate_macro_attributes(&parsed(source)).unwrap();
    let attributes = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { attributes, .. } => Some((
                attributes.get_str("label").map(str::to_owned),
                attributes.get("macro-rec").is_some(),
                attributes.get("simplification").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(attributes);
    });
}

#[test]
fn guards_or_patterns_with_collision_free_typed_aliases() {
    let source = indoc! {r##"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | Exp "#Or" Exp [symbol(#Or)]
          rule a #Or b
        endmodule
    "##};
    let transformed = guard_or_patterns(&parsed(source)).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_generated_by(&transformed, GeneratingPass::GuardOrPatterns);
}

#[test]
fn or_guards_do_not_cross_existing_alias_or_rewrite_boundaries() {
    let or = Term::Apply {
        label: Label::with_parameters("#Or", vec![Sort::new("Exp")]),
        arguments: vec![application("a", Vec::new()), application("b", Vec::new())],
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("a", "Exp", Attributes::default()),
                production("b", "Exp", Attributes::default()),
                rule(rewrite(or.clone(), or.clone()), Attributes::default()),
                Sentence::Context {
                    body: Term::As {
                        pattern: Box::new(or),
                        alias: Box::new(Term::variable("X")),
                    },
                    requires: truth(),
                    attributes: Attributes::default(),
                },
            ],
        )],
        attributes: Attributes::default(),
    };
    assert_eq!(guard_or_patterns(&definition).unwrap(), definition);
}

#[test]
fn allocates_shared_and_anonymous_fresh_configuration_constants() {
    let source = indoc! {r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Int ::= r"[0-9]+" [token]
          syntax Int ::= "initA" [function, initializer, symbol(initA)]
                       | "initB" [function, initializer, symbol(initB)]
          rule initA => !X:Int [initializer]
          rule initB => !X:Int [initializer]
          rule initA => !_ [initializer]
          rule initB => !_ [initializer]
        endmodule
    "#};
    let definition = resolve_anon_vars(&parsed(source));
    let definition = resolve_semantic_casts(&definition);
    let (transformed, next_fresh) = resolve_fresh_config_constants(&definition).unwrap();
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();
    let output = (bodies, next_fresh);

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_generated_by(&transformed, GeneratingPass::ResolveFreshConfigConstants);
}

#[test]
fn rejects_non_integer_fresh_configuration_constants() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::Rule {
                body: rewrite(
                    application("init", Vec::new()),
                    Term::Variable {
                        name: "!Fresh".into(),
                        sort: Some(Sort::new("String")),
                    },
                ),
                requires: truth(),
                ensures: truth(),
                attributes: attributes(&[("initializer", json!(""))]),
            }],
        )],
        attributes: Attributes::default(),
    };
    let error = resolve_fresh_config_constants(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].message,
        "Can't resolve fresh configuration variable not of sort Int"
    );
}

#[test]
fn generates_predicates_for_each_local_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool
          syntax Exp ::= "a" [symbol(a)]
          syntax Data ::= "d" [symbol(d)]
        endmodule
    "#};
    let transformed = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let predicates = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                sort,
                attributes,
                ..
            } if attributes.get("predicate").is_some() => Some((
                label.name.clone(),
                sort.to_string(),
                attributes.get("predicate").cloned(),
                attributes.get("total").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(predicates);
    });
    assert_generated_by(&transformed, GeneratingPass::GenerateSortPredicateSyntax);
}

#[test]
fn generates_generic_and_named_field_projections() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Pair ::= pair(left: Int, right: Int) [symbol(pair)]
        endmodule
    "#};
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let transformed = generate_sort_projections(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name.starts_with("project:") => Some((
                "production",
                label.name.clone(),
                attributes.get("total").is_some(),
                attributes.get("projection").is_some(),
            )),
            Sentence::Rule {
                body, attributes, ..
            } if Printer::new().print_term(body).starts_with("`project:") => Some((
                "rule",
                Printer::new().print_term(body),
                attributes.get("total").is_some(),
                attributes.get("projection").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_has_generated_by(&transformed, GeneratingPass::GenerateSortProjections);
}

#[test]
fn generated_sort_projections_are_idempotent() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![Sentence::SyntaxSort {
                parameters: Vec::new(),
                sort: Sort::new("Exp"),
                attributes: Attributes::default(),
            }],
        )],
        attributes: Attributes::default(),
    };
    let definition = generate_sort_predicate_syntax(&definition).unwrap();
    let once = generate_sort_projections(&definition).unwrap();
    let twice = generate_sort_projections(&once).unwrap();
    assert_eq!(once, twice);
}

#[test]
fn expands_nested_macros_child_first_in_priority_order() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "c" [symbol(c)]
                       | "m(" Exp ")" [macro, symbol(m)]
                       | "n(" Exp ")" [macro-rec, symbol(n)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
          rule m(X:Exp) => n(X:Exp) [priority(10)]
          rule n(a) => b [priority(20)]
          rule n(b) => c [owise]
          rule pair(m(a), n(b)) => pair(n(a), m(b)) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .next()
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_has_generated_by(&transformed, GeneratingPass::MacroExpansion);
}

#[test]
fn simplification_rules_do_not_inherit_macro_kinds_during_expansion() {
    for macro_kind in ["macro", "macro-rec", "alias", "alias-rec"] {
        let source = format!(
            r#"
                module MAIN
                  syntax Exp ::= "a" [symbol(a)]
                               | "f(" Exp ")" [function, symbol(f)]
                               | "m(" Exp ")" [{macro_kind}, symbol(m)]
                  rule m(a) => f(a) [simplification]
                endmodule
            "#,
        );
        let definition = resolve_semantic_casts(&parsed(&source));
        let definition = propagate_macro_attributes(&definition).unwrap();

        let error = expand_macros(&definition).unwrap_err();
        assert_eq!(
            error.diagnostics[0].message, "Rule contains macro symbol that was not expanded",
            "production attribute {macro_kind}",
        );
        assert_eq!(
            expand_macros_in_term(
                &definition,
                "MAIN",
                application("m", vec![application("a", Vec::new())]),
            )
            .unwrap(),
            application("m", vec![application("a", Vec::new())]),
            "production attribute {macro_kind}",
        );
    }
}

#[test]
fn ordinary_rules_still_inherit_every_macro_kind_during_term_expansion() {
    for macro_kind in ["macro", "macro-rec", "alias", "alias-rec"] {
        let source = format!(
            r#"
                module MAIN
                  syntax Exp ::= "a" [symbol(a)]
                               | "f(" Exp ")" [symbol(f)]
                               | "m(" Exp ")" [{macro_kind}, symbol(m)]
                  rule m(a) => f(a)
                endmodule
            "#,
        );
        let definition = resolve_semantic_casts(&parsed(&source));

        assert_eq!(
            expand_macros_in_term(
                &definition,
                "MAIN",
                application("m", vec![application("a", Vec::new())]),
            )
            .unwrap(),
            application("f", vec![application("a", Vec::new())]),
            "production attribute {macro_kind}",
        );
    }
}

#[test]
fn explicit_simplification_macro_does_not_inherit_recursive_kind() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
                       | "m(" Exp ")" [macro-rec, symbol(m)]
          rule m(pair(X:Exp, Y:Exp)) => m(X:Exp) [macro, simplification]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let term = application(
        "m",
        vec![application(
            "pair",
            vec![
                application(
                    "pair",
                    vec![application("a", Vec::new()), application("b", Vec::new())],
                ),
                application("b", Vec::new()),
            ],
        )],
    );

    assert_eq!(
        expand_macros_in_term(&definition, "MAIN", term).unwrap(),
        application(
            "m",
            vec![application(
                "pair",
                vec![application("a", Vec::new()), application("b", Vec::new())],
            )],
        ),
    );
}

#[test]
fn macro_expansion_preserves_an_unrelated_simplification_equation() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [function, symbol(f)]
          rule f(a) => a [simplification, label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => Some(body),
            _ => None,
        })
        .unwrap();

    assert_eq!(Printer::new().print_term(body), "f(a(.KList))=>a(.KList)");
}

#[test]
fn imported_macro_expansion_preserves_template_and_caller_production_identity() {
    // The same label has two productions. An imported macro must keep its own
    // production, while a substituted argument keeps the caller's production.
    let source = indoc! {r#"
        module A-EXTRA
          syntax Other ::= "other" [symbol(other)]
                         | "otherBox(" Other ")" [symbol(box)]
        endmodule
        module DATA
          syntax Exp ::= "a" [symbol(a)]
                       | "box(" Exp ")" [symbol(box)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => box(X:Exp)
          rule box(m(a)) => a [label(local)]
        endmodule
        module MAIN
          imports A-EXTRA
          imports DATA
          syntax Exp ::= "caller" [symbol(caller)]
          rule box(m(caller)) => a [label(imported)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let resolved = ResolvedDefinition::resolve(&transformed).unwrap();
    for (module_name, rule_label, argument_label) in
        [("DATA", "local", "a"), ("MAIN", "imported", "caller")]
    {
        let module_id = resolved.module_id(module_name).unwrap();
        let catalog = resolved.production_catalog(module_id);
        let body = resolved
            .module(module_id)
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule {
                    body, attributes, ..
                } if attributes.get_str("label") == Some(rule_label) => Some(body),
                _ => None,
            })
            .unwrap();
        let Term::Rewrite { left, .. } = body.unannotated() else {
            panic!("expected rewrite")
        };
        let Term::Apply { arguments, .. } = left.unannotated() else {
            panic!("expected outer box")
        };
        let expanded = &arguments[0];
        let Term::Apply { label, arguments } = expanded.unannotated() else {
            panic!("expected expanded box")
        };
        assert_eq!(label.name, "box");
        let production = expanded.metadata().unwrap().production.unwrap();
        assert!(
            matches!(catalog.production(ProductionId(production.0)),
            Sentence::Production { label: Some(label), sort, .. }
                if label.name == "box" && sort == &Sort::new("Exp")),
            "{module_name}: expanded macro must retain the Exp overload"
        );
        let argument = &arguments[0];
        let production = argument.metadata().unwrap().production.unwrap();
        assert!(
            matches!(catalog.production(ProductionId(production.0)),
            Sentence::Production { label: Some(label), .. } if label.name == argument_label),
            "{module_name}: substitution must retain its caller's production"
        );
    }
}

#[test]
fn macro_expansion_combines_call_site_and_macro_rule_sources() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => b
          rule m(a) [label(subject)]
        endmodule
    "#};
    let span = |text: &str, from: usize| {
        let start = from + source[from..].find(text).unwrap();
        ProvenanceLink::Source {
            span: TermSpan {
                source: SourceId(0),
                start,
                end: start + text.len(),
            },
        }
    };
    let macro_rule = source.find("rule m(X:Exp) => b").unwrap();
    let subject = source.find("rule m(a)").unwrap();
    let call_site = span("m(a)", subject);
    let macro_rhs = span("b", macro_rule);
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => Some(body),
            _ => None,
        })
        .unwrap();
    let origins = &body
        .metadata()
        .and_then(|metadata| metadata.origin.as_deref())
        .unwrap()
        .origins;

    let macro_rhs_index = origins.iter().position(|link| link == &macro_rhs).unwrap();
    let call_site_index = origins.iter().position(|link| link == &call_site).unwrap();
    assert!(macro_rhs_index < call_site_index, "{origins:#?}");
    assert_eq!(
        origins
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        origins.len(),
        "{origins:#?}",
    );
}

#[test]
fn expands_smt_lemma_aliases_before_backend_validation() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | "constant" [alias, symbol(constant)]
                       | "f(" Int ")" [function, total, smtlib(f), symbol(f)]
          rule constant => 2
          rule f(I:Int) => f(constant) [smt-lemma]
        endmodule
    "#};
    let definition = propagate_macro_attributes(&parsed(source)).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("smt-lemma").is_some() => Some(body),
            _ => None,
        })
        .unwrap();

    assert!(!Printer::new().print_term(body).contains("constant"));
}

#[test]
fn macro_matching_reuses_repeated_variables_and_freshens_unbound_rhs_variables() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "same(" Exp "," Exp ")" [macro, symbol(same)]
                       | "choose(" Exp ")" [macro, symbol(choose)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
          rule same(X:Exp, X:Exp) => X:Exp
          rule choose(X:Exp) => pair(X:Exp, Y:Exp)
          rule pair(same(a, a), choose(a)) => pair(a, a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => Some(body),
            _ => None,
        })
        .unwrap();
    let printed = Printer::new().print_term(body);
    assert!(printed.contains("pair(a(.KList),_Gen0)"), "{printed}");
}

#[test]
fn reports_a_macro_symbol_when_repeated_variable_matching_fails() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "same(" Exp "," Exp ")" [macro, symbol(same)]
          rule same(X:Exp, X:Exp) => X:Exp
          rule same(a, b) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].message,
        "Rule contains macro symbol that was not expanded"
    );
}

#[test]
fn expands_sort_constrained_variable_macros_over_tokens() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= r"[a-z]+" [prec(3), token]
          syntax Exp ::= "wrap(" Foo ")" [symbol(wrap)]
          rule X:Foo => bar [macro]
          rule wrap(foo) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn rejects_macro_side_conditions_and_invalid_priorities() {
    let side_condition = indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token] | "false" [token]
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => X:Exp requires false
          rule m(a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(side_condition));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).unwrap_err();
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.message == "Cannot compute macros with side conditions.")
    );

    let invalid_priority = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => X:Exp [priority(not-an-integer)]
          rule m(a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(invalid_priority));
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].message,
        "Invalid value for priority attribute: not-an-integer. Must be an integer."
    );
}

#[test]
fn wraps_cell_free_rules_and_contexts_in_the_main_computation_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
                       | "f(" Exp ")" [function, symbol(f)]
                       | "g(" Exp ")" [symbol(g)]
          configuration <k> 0 </k>
          rule 1 => 2 [label(bare)]
          rule <k> 1 => 2 ... </k> [label(cell)]
          rule f(1) => 2 [label(function)]
          rule g(1) => 2 [anywhere, label(anywhere)]
          rule g(2) => 1 [simplification, label(simplification)]
          context g(HOLE) [label(context)]
          syntax K
          syntax Map
        endmodule
    "#};
    let transformed = add_implicit_computation_cell(&parsed(source)).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            }
            | Sentence::Context {
                body, attributes, ..
            } => attributes
                .get_str("label")
                .map(|label| (label.to_owned(), Printer::new().print_term(body))),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_has_generated_by(&transformed, GeneratingPass::AddImplicitComputationCell);
}

#[test]
fn wraps_only_the_generated_counter_two_item_claim() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)] | "b" [symbol(b)]
          configuration <k> a </k> <state> a </state>
          syntax K
          syntax Map
        endmodule
    "#};
    let item = rewrite(application("a", Vec::new()), application("b", Vec::new()));
    let counter_body = application(
        "#cells",
        vec![
            item.clone(),
            incomplete_cell("<generatedCounter>", Term::variable("GC")),
        ],
    );
    let state_body = application(
        "#cells",
        vec![
            item.clone(),
            incomplete_cell("<state>", Term::variable("STATE")),
        ],
    );
    let mut definition = parsed(source);
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .extend([
            Sentence::Claim {
                body: counter_body,
                requires: truth(),
                ensures: truth(),
                attributes: attributes(&[("label", json!("counter-sentinel"))]),
            },
            Sentence::Claim {
                body: state_body.clone(),
                requires: truth(),
                ensures: truth(),
                attributes: attributes(&[("label", json!("ordinary-second-cell"))]),
            },
        ]);

    let transformed = add_implicit_computation_cell(&definition).unwrap();
    let claims = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Claim {
                body, attributes, ..
            } => attributes.get_str("label").map(|label| (label, body)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    assert_eq!(claims["counter-sentinel"], &incomplete_cell("<k>", item));
    assert_eq!(claims["ordinary-second-cell"], &state_body);
}

#[test]
fn imported_syntax_rules_use_the_main_modules_computation_cell() {
    let source = indoc! {r#"
        module LANGUAGE-SYNTAX
          syntax Int ::= r"[0-9]+" [token]
          rule 1 => 2 [label(imported)]
        endmodule

        module MAIN
          imports LANGUAGE-SYNTAX
          configuration <k> 0 </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let transformed = add_implicit_computation_cell(&parsed(source)).unwrap();
    let body = transformed
        .modules
        .iter()
        .find(|module| module.name == "LANGUAGE-SYNTAX")
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("imported") => Some(body),
            _ => None,
        })
        .unwrap();

    assert!(matches!(
        body.unannotated(),
        Term::Apply { label, .. } if label.name == "<k>"
    ));
}

#[test]
fn wraps_a_non_function_overload_in_the_computation_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(shared)]
                       | "f" [function, symbol(shared)]
                       | "done" [symbol(done)]
          configuration <k> a </k>
          rule a => done [label(step)]
          rule f => a [label(equation)]
          syntax K
          syntax Map
        endmodule
    "#};
    let transformed = add_implicit_computation_cell(&parsed(source)).unwrap();
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => attributes.get_str("label").map(|label| (label, body)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    assert!(matches!(
        bodies["step"].unannotated(),
        Term::Apply { label, .. } if label.name == "<k>"
    ));
    assert!(matches!(
        bodies["equation"].unannotated(),
        Term::Rewrite { left, .. }
            if matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "shared")
    ));
}

#[test]
fn falls_back_safely_when_function_application_metadata_is_stale() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f" [function, symbol(f)]
                       | "done" [symbol(done)]
          configuration <k> a </k>
          rule a => done [label(step)]
          rule f => done [label(equation)]
          syntax K
          syntax Map
        endmodule
    "#};
    let mut definition = parsed(source);
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let catalog = resolved.production_catalog(resolved.main_module_id());
    let a = catalog.productions_for(&LabelHead::from(&Label::new("a")))[0];
    let f = catalog.productions_for(&LabelHead::from(&Label::new("f")))[0];

    let main = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap();
    for sentence in &mut main.local_sentences {
        let Sentence::Rule {
            body, attributes, ..
        } = sentence
        else {
            continue;
        };
        let Some(rule_label) = attributes.get_str("label") else {
            continue;
        };
        let Term::Rewrite { left, right } = body.unannotated() else {
            unreachable!()
        };
        let stale = if rule_label == "step" { f } else { a };
        let annotated = left.as_ref().clone().with_metadata(TermMetadata {
            production: Some(ResolvedProductionId(stale.0)),
            ..TermMetadata::default()
        });
        let rebuilt = Term::Rewrite {
            left: Box::new(annotated),
            right: right.clone(),
        };
        *body = if let Some(metadata) = body.metadata().cloned() {
            rebuilt.with_metadata(metadata)
        } else {
            rebuilt
        };
    }

    let transformed = add_implicit_computation_cell(&definition).unwrap();
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => attributes.get_str("label").map(|label| (label, body)),
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();

    assert!(matches!(
        bodies["step"].unannotated(),
        Term::Apply { label, .. } if label.name == "<k>"
    ));
    assert!(matches!(
        bodies["equation"].unannotated(),
        Term::Rewrite { left, .. }
            if matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "f")
    ));
}

#[test]
fn implicit_computation_cells_require_a_declared_main_cell_only_when_needed() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                rewrite(application("a", Vec::new()), application("b", Vec::new())),
                Attributes::default(),
            )],
        )],
        attributes: Attributes::default(),
    };
    assert_eq!(
        add_implicit_computation_cell(&definition).unwrap_err(),
        "No main cell found"
    );

    let skipped = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![rule(
                application("a", Vec::new()),
                attributes(&[("anywhere", json!(""))]),
            )],
        )],
        attributes: Attributes::default(),
    };
    assert_eq!(add_implicit_computation_cell(&skipped).unwrap(), skipped);
}

#[test]
fn resolves_fresh_variables_and_generates_the_counter_configuration() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int | Id
                       | "pair(" Id "," Id ")" [symbol(pair)]
          syntax Id ::= r"[a-z]+" [token]
                      | "freshId(" Int ")" [function, freshGenerator, symbol(freshId)]
          configuration <k> 0 </k>
          rule 0 => pair(!Y:Id, !X:Id) [label(fresh)]
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let transformed = resolve_fresh_constants(&definition, 7).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label),
                sort,
                items,
                attributes,
                ..
            } if matches!(
                label.name.as_str(),
                "<generatedTop>" | "<generatedCounter>" | "getGeneratedCounterCell"
            ) =>
            {
                Some(format!(
                    "production {} : {sort} ({} items) format={:?}",
                    label.name,
                    items.len(),
                    attributes.get_str("format")
                ))
            }
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("fresh") => {
                Some(format!("rule {}", Printer::new().print_term(body)))
            }
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_some()
                && Printer::new()
                    .print_term(body)
                    .starts_with("initGeneratedTopCell") =>
            {
                Some(format!("initializer {}", Printer::new().print_term(body)))
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_has_generated_by(&transformed, GeneratingPass::ResolveFreshConstants);
}

#[test]
fn fresh_offsets_reuse_names_and_cover_the_counter_range() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | "freshInt(" Int ")" [function, freshGenerator, symbol(freshInt)]
          syntax Exp ::= Int
                       | "triple(" Int "," Int "," Int ")" [symbol(triple)]
          configuration <k> 0 </k>
          rule 0 => triple(!B:Int, !Q:Int, !B:Int) [label(fresh-range)]
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let transformed = resolve_fresh_constants(&definition, 7).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("fresh-range") => Some(body),
            _ => None,
        })
        .expect("fresh-range rule should remain present");

    assert_eq!(
        Printer::new().print_term(body),
        "#cells(`<k>`(#noDots(.KList),#token(\"0\",\"Int\")=>triple(freshInt(`_+Int_`(#Fresh,#token(\"0\",\"Int\"))),freshInt(`_+Int_`(#Fresh,#token(\"1\",\"Int\"))),freshInt(`_+Int_`(#Fresh,#token(\"0\",\"Int\")))),#dots(.KList)),`<generatedCounter>`(#noDots(.KList),#Fresh=>`_+Int_`(#Fresh,#token(\"2\",\"Int\")),#noDots(.KList)))"
    );
}

#[test]
fn expands_the_internally_generated_counter_configuration() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> 0 </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let transformed = resolve_fresh_constants(&definition, 0)
        .expect("K's generated counter cell must bypass the user-name reservation");

    assert!(
        transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(
                sentence,
                Sentence::Production { label: Some(label), .. }
                    if label.name == "<generatedCounter>"
            ))
    );
}

#[test]
fn preserves_explicit_cell_variables_while_sorting_cell_fragments() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Id ::= "freshId(" Int ")" [function, freshGenerator, symbol(freshId)]
          configuration <k> 0 </k>
          rule 0 => !X:Id
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. }
                if Printer::new()
                    .print_term(body)
                    .starts_with("getGeneratedCounterCell") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("counter projection rule should be generated");

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(body);
    });
}

#[test]
fn reports_missing_generators_for_fresh_variables() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
          configuration <k> a </k>
          rule a => !X:Exp [label(fresh)]
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let error = resolve_fresh_constants(&definition, 0).unwrap_err();
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message == "No fresh generator defined for sort Exp" })
    );
}

#[test]
fn reports_fresh_variables_without_sorts() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::Production {
                    label: Some(Label::new("<generatedTop>")),
                    parameters: Vec::new(),
                    sort: Sort::new("GeneratedTopCell"),
                    items: vec![
                        ProductionItem::Terminal("<generatedTop>".into()),
                        ProductionItem::NonTerminal {
                            sort: Sort::new("K"),
                            name: None,
                        },
                        ProductionItem::Terminal("</generatedTop>".into()),
                    ],
                    attributes: attributes(&[
                        ("cell", json!("")),
                        ("cellName", json!("generatedTop")),
                    ]),
                },
                rule(
                    rewrite(application("a", Vec::new()), Term::variable("!X")),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let error = resolve_fresh_constants(&definition, 0).unwrap_err();
    assert!(error.diagnostics.iter().any(|diagnostic| {
        diagnostic.message == "Fresh constant used without a declared sort."
    }));
}

#[test]
fn simplification_rules_require_functional_heads() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [function, symbol(f)]
                       | "w(" Exp ")" [functional, symbol(w)]
                       | "m(" Exp ")" [mlOp, symbol(m)]
                       | "c(" Exp ")" [symbol(c)]
          rule f(a) => a [simplification, label(function)]
          rule w(a) => a [simplification, label(functional)]
          rule m(a) => a [simplification, label(ml)]
        endmodule
    "#};
    assert_eq!(
        check_simplification_rules(&parsed(source)).unwrap(),
        parsed(source)
    );

    let invalid = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "c(" Exp ")" [symbol(c)]
          rule c(a) => a [simplification, label(invalid)]
        endmodule
    "#};
    let error = check_simplification_rules(&parsed(invalid)).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Simplification rules expect function/functional/mlOp symbols at the top of the left hand side term."
    );
}

#[test]
fn concretizes_nested_cells_to_declared_fixed_arities() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          configuration
            <top>
              <k> 0 </k>
              <state> 1 </state>
            </top>
          rule <k> 0 => 1 ... </k>
          rule <state> 1 => 2 </state>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none()
                && (Printer::new().print_term(body).contains("#token(\"0\"")
                    || Printer::new().print_term(body).contains("#token(\"2\"")) =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .collect::<Vec<_>>();

    assert!(
        !output.iter().any(|body| body.contains("#dots")),
        "{output:#?}"
    );
    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
    assert_has_generated_by(&transformed, GeneratingPass::ConcretizeCells);
}

#[test]
fn concretizes_main_configuration_with_an_auxiliary_initializer() {
    for auxiliary in ["1", "<baz> 1 </baz>"] {
        let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> $PGM:K </k> <foo> 0 </foo>
          configuration <bar> AUXILIARY </bar>
          rule <k> I:Int => initBarCell ... </k> <foo> I </foo> [label(step)]
          syntax K
          syntax Map
        endmodule
    "#}
        .replace("AUXILIARY", auxiliary);
        let definition = parsed(&source);
        let definition = resolve_semantic_casts(&definition);
        let definition = add_implicit_computation_cell(&definition).unwrap();
        let definition = resolve_fresh_constants(&definition, 0).unwrap();
        let transformed = concretize_cells(&definition).unwrap();
        let rules = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter_map(|sentence| match sentence {
                Sentence::Rule { body, .. } => Some(body.to_string()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            rules
                .iter()
                .any(|body| body.contains("initBarCell(.KList)") && body.contains("<bar>"))
        );
        let step = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule {
                    body, attributes, ..
                } if attributes.get_str("label") == Some("step") => Some(body),
                _ => None,
            })
            .unwrap();
        assert!(
            matches!(step.unannotated(), Term::Apply { label, .. }
            if label.name == "<generatedTop>"),
            "{step}"
        );
        let step = step.to_string();
        assert!(step.contains("initBarCell(.KList)"), "{step}");
        assert!(!step.contains("#dots"), "{step}");
    }
}

#[test]
fn rejects_multiple_configuration_roots_without_a_generated_top() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> $PGM:K </k>
          configuration <bar> 1 </bar>
          syntax K
          syntax Map
        endmodule
    "#});
    let error = resolve_fresh_constants(&definition, 0).unwrap_err();
    assert!(error.diagnostics.iter().any(
        |diagnostic| diagnostic.message == "Too many top cells for module MAIN: BarCell, KCell"
    ));
}

#[test]
fn preserves_already_complete_nested_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "inspect" "(" TopCell ")" [function, symbol(inspect)]
          configuration
            <top>
              <k> 0 </k>
              <state> 1 </state>
            </top>
          rule inspect(T:TopCell) => inspect(T:TopCell)
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let mut definition = resolve_fresh_constants(&definition, 0).unwrap();
    let complete_top = application(
        "<top>",
        vec![
            application(
                "<k>",
                vec![Term::Token {
                    token: "0".into(),
                    sort: Sort::new("Int"),
                }],
            ),
            application(
                "<state>",
                vec![Term::Token {
                    token: "1".into(),
                    sort: Sort::new("Int"),
                }],
            ),
        ],
    );
    let mut replaced = false;
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .expect("the main module should be present");
    for sentence in &mut module.local_sentences {
        if let Sentence::Rule { body, .. } = sentence
            && Printer::new().print_term(body).contains("inspect")
        {
            let inspection = application("inspect", vec![complete_top.clone()]);
            *body = rewrite(inspection.clone(), inspection);
            replaced = true;
            break;
        }
    }
    assert!(replaced, "the authored inspect rule should be present");

    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } if Printer::new().print_term(body).contains("inspect") => {
                Some(body)
            }
            _ => None,
        })
        .expect("the inspect rule should survive concretization");
    let Term::Rewrite { left, .. } = body.unannotated() else {
        panic!("the inspect rule should remain a rewrite")
    };
    let Term::Apply {
        label,
        arguments: inspect_arguments,
    } = left.unannotated()
    else {
        panic!("the rewrite left side should remain an application")
    };
    assert_eq!(label.name, "inspect");
    let [top] = inspect_arguments.as_slice() else {
        panic!("inspect should retain one argument")
    };
    let Term::Apply {
        label,
        arguments: top_arguments,
    } = top.unannotated()
    else {
        panic!("inspect should retain its complete top cell")
    };
    assert_eq!(label.name, "<top>");
    assert_eq!(top_arguments.len(), 2);
    assert!(top_arguments.iter().all(|argument| {
        matches!(argument.unannotated(), Term::Apply { arguments, .. } if arguments.len() == 1)
    }));
    assert!(!Printer::new().print_term(body).contains("#dots"));
}

#[test]
fn complete_cells_are_rejected_with_a_typed_error() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <k> 0 </k>
              <state> 0 </state>
              <output> 0 </output>
            </top>
          rule <k> 0 => 1 </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let child = || application("<k>", vec![Term::variable("K")]);
    let cases = [
        (
            "one complete child",
            vec![child()],
            "Expected incomplete cell with 3 arguments, found 1",
        ),
        (
            "three complete children",
            vec![child(), child(), child()],
            "Expected #dots() or #noDots() in incomplete cell",
        ),
    ];

    for (name, arguments, expected) in cases {
        let mut input = definition.clone();
        let rule = input
            .modules
            .iter_mut()
            .find(|module| module.name == "MAIN")
            .unwrap()
            .local_sentences
            .iter_mut()
            .find(|sentence| {
                matches!(sentence, Sentence::Rule { attributes, .. }
                    if attributes.get("initializer").is_none())
            })
            .expect("fixture has an ordinary rule");
        let Sentence::Rule { body, .. } = rule else {
            unreachable!()
        };
        *body = application("<top>", arguments);

        let error = match concretize_cells(&input) {
            Err(error) => error,
            Ok(_) => panic!("{name} unexpectedly concretized"),
        };
        assert_eq!(error.diagnostics.len(), 1, "{name}: {error:#?}");
        assert!(
            error.diagnostics[0].message.contains(expected),
            "{name}: {error:#?}"
        );
    }
}

#[test]
fn drops_a_shallower_misnested_sibling_when_completing_parent_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <left>
                <value> 0 </value>
              </left>
              <right> 1 </right>
            </top>
          rule
            <left>
              <value> 0 => 2 </value>
              <right> 1 => 3 </right>
              ...
            </left>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none()
                && Printer::new().print_term(body).contains("#token(\"2\"") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("the labeled rule should remain");

    assert!(
        body.contains("<value>"),
        "the direct child was lost: {body}"
    );
    assert!(
        !body.contains("<right>"),
        "the shallower sibling should match Java's discarded level: {body}"
    );
}

fn omitted_thread_parent_fixture(rule: &str) -> Definition {
    let source = format!(
        r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <thread multiplicity="*">
                <k> 0 </k>
                <state> 0 </state>
              </thread>
            </top>
          rule {rule}
          syntax K
          syntax Map
        endmodule
        "#,
    );
    let definition = resolve_semantic_casts(&parsed(&source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    resolve_fresh_constants(&definition, 0).unwrap()
}

#[test]
fn omitted_parents_separate_repeated_nonmultiplicity_children() {
    let definition = omitted_thread_parent_fixture("<k> 0 => 1 ... </k> <k> 2 => 3 ... </k>");
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .expect("the rendezvous-shaped rule should remain");
    assert_eq!(body.matches("`<thread>`(").count(), 2, "{body}");
    assert_eq!(body.matches("`<k>`(").count(), 2, "{body}");
    assert_eq!(body.matches("=>").count(), 2, "{body}");
    assert!(!body.contains("#dots"), "{body}");
}

#[test]
fn omitted_parents_group_distinct_nonmultiplicity_children() {
    let definition = omitted_thread_parent_fixture("<k> 0 => 1 ... </k> <state> 2 => 3 </state>");
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .expect("the rule should remain");
    assert_eq!(body.matches("`<thread>`(").count(), 1, "{body}");
    assert_eq!(body.matches("`<k>`(").count(), 1, "{body}");
    assert_eq!(body.matches("`<state>`(").count(), 1, "{body}");
    assert_eq!(body.matches("=>").count(), 2, "{body}");
}

#[test]
fn omitted_parents_reject_ambiguous_mixed_child_partition() {
    let definition =
        omitted_thread_parent_fixture("<k> 0 => 1 ... </k> <k> 2 => 3 ... </k> <state> 4 </state>");
    let error = concretize_cells(&definition).unwrap_err();
    assert!(
        error
            .diagnostics
            .iter()
            .any(|diagnostic| { diagnostic.message.contains("Ambiguous completion") }),
        "the state cell could belong to either thread: {error:#?}"
    );
}

#[test]
fn omitted_parents_check_conflicts_on_each_rewrite_side() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <thread multiplicity="*">
                <k> 0 </k>
                <state multiplicity="?"> 0 </state>
              </thread>
            </top>
          rule <k> 0 => 1 ... </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    // These are parser-shaped cell rewrites. Empty sides carry no cell sort;
    // each insertion or removal is forced into its own omitted thread parent.
    for insert in [false, true] {
        let mut input = definition.clone();
        let body = input
            .modules
            .iter_mut()
            .find(|module| module.name == "MAIN")
            .unwrap()
            .local_sentences
            .iter_mut()
            .find_map(|sentence| match sentence {
                Sentence::Rule {
                    body, attributes, ..
                } if attributes.get("initializer").is_none() => Some(body),
                _ => None,
            })
            .unwrap();
        *body = application(
            "#cells",
            ["1", "2"]
                .into_iter()
                .map(|value| {
                    let state = application(
                        "<state>",
                        vec![
                            application("#noDots", Vec::new()),
                            Term::Token {
                                token: value.into(),
                                sort: Sort::new("Int"),
                            },
                            application("#noDots", Vec::new()),
                        ],
                    );
                    let empty = application("#cells", Vec::new());
                    if insert {
                        rewrite(empty, state)
                    } else {
                        rewrite(state, empty)
                    }
                })
                .collect(),
        );
        let transformed = concretize_cells(&input).unwrap();
        let body = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule {
                    body, attributes, ..
                } if attributes.get("initializer").is_none() => {
                    Some(Printer::new().print_term(body))
                }
                _ => None,
            })
            .unwrap();
        assert_eq!(
            body.matches("`<thread>`(").count(),
            2,
            "insert={insert}: {body}"
        );
        assert_eq!(
            body.matches("`<state>`(").count(),
            2,
            "insert={insert}: {body}"
        );
        assert_eq!(body.matches("=>").count(), 2, "insert={insert}: {body}");
    }
}

#[test]
fn concretizes_cells_inside_generated_simplification_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <batch> 0 </batch>
            </top>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();

    for sentence in transformed
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        let Sentence::Rule { body, .. } = sentence else {
            continue;
        };
        body.visit_preorder(&mut |term| {
            if let Term::Apply { label, arguments } = term.unannotated()
                && label.name == "<batch>"
            {
                assert_eq!(arguments.len(), 1, "incomplete batch cell in {body:?}");
            }
        });
    }

    let transformed = add_semantics_module(&transformed).unwrap();
    let transformed = resolve_config_var(&transformed);
    let transformed = add_cool_like_attributes(&transformed);
    let transformed = generate_sort_predicate_rules(&transformed);
    let transformed = number_sentences(&transformed);
    add_sort_injections_to_definition(&transformed).unwrap();
}

#[test]
fn concretizes_authored_simplification_cell_bodies_without_root_wrapping() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <batch> 0 </batch>
            </top>
          rule <batch> 0 => 1 </batch> [simplification]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("simplification").is_some() => Some(body),
            _ => None,
        })
        .expect("the authored simplification rule should remain");

    let mut batch_arities = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::Apply { label, arguments } = term.unannotated()
            && label.name == "<batch>"
        {
            batch_arities.push(arguments.len());
        }
    });
    assert_eq!(batch_arities, [1], "incomplete batch cell in {body:?}");
    assert!(
        !Printer::new().print_term(body).contains("<generatedTop>"),
        "simplification rule gained a generated top cell: {body:?}"
    );
}

#[test]
fn does_not_wrap_matching_logic_simplifications_in_the_generated_top_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [mlOp, symbol(m)]
          configuration <k> a </k>
          rule m(a) => a [simplification]
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("simplification").is_some() => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .expect("the simplification rule should remain");

    assert!(body.starts_with("m("), "rule was wrapped in a cell: {body}");
    assert!(
        !body.contains("<generatedTop>"),
        "simplification rule gained the generated top cell: {body}"
    );
}

#[test]
fn splits_fragment_variables_on_both_sides_of_a_parent_cell_rewrite() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <k> 0 </k>
              <saved>
                <first> 1 </first>
                <second> 2 </second>
              </saved>
            </top>
          rule <k> 0 => 1 ... </k>
               <saved> _ => SAVED </saved>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_anon_vars(&parsed(source));
    let definition = resolve_semantic_casts(&definition);
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();

    assert!(
        body.contains("<saved>"),
        "missing saved parent cell: {body}"
    );
    assert_eq!(
        body.matches("=>").count(),
        3,
        "the k, first, and second cells should each contain a rewrite: {body}"
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn lifts_one_sided_repeated_cell_rewrites_through_missing_parents() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <store>
                <items>
                  <item multiplicity="*" type="Map">
                    <id> 0 </id>
                  </item>
                </items>
              </store>
            </top>
          rule (.Bag => <item> <id> 1 </id> </item>)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .expect("the repeated-cell insertion rule should remain");

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(body);
    });
}

#[test]
fn clears_repeated_cell_contents_without_removing_the_parent() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <items>
                <item multiplicity="*" type="Map">
                  <id> 0 </id>
                </item>
              </items>
            </top>
          rule <items> _ => .Bag </items>
        endmodule
    "#};
    let definition = resolve_anon_vars(&parsed(source));
    let definition = resolve_semantic_casts(&definition);
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .expect("the repeated-cell clearing rule should remain");

    assert!(
        body.contains("`<items>`("),
        "the parent cell was removed: {body}"
    );
    assert!(
        body.contains("=>`.ItemCellMap`"),
        "the repeated contents were not cleared: {body}"
    );
}

#[test]
fn splits_cell_fragment_variables_on_both_sides_of_a_rewrite() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <callState>
                <program> 0 </program>
                <status> 1 </status>
              </callState>
            </top>
          rule <callState> _ => CALLSTATE </callState>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none() => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(body);
    });
}

#[cfg(feature = "z3-inference")]
#[test]
fn concretizes_cells_inside_simplification_rules_without_adding_a_top_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <batch> 0 </batch>
            </top>
          rule <batch> 0 => 1 </batch>
            requires <batch> 0 </batch> :=K <batch> 0 </batch>
            [simplification]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                attributes,
                ..
            } if attributes.get("simplification").is_some() => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
            )),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn concretizes_unrelated_modules_with_their_local_cell_models() {
    let source = indoc! {r#"
        module OTHER
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <other>
              <batch> 0 </batch>
            </other>
        endmodule

        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> 0 </top>
        endmodule
    "#};
    let transformed = concretize_cells(&parsed(source)).unwrap();
    let initializer = transformed
        .modules
        .iter()
        .find(|module| module.name == "OTHER")
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_some()
                && Printer::new().print_term(body).starts_with("initBatchCell") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_snapshot!(initializer);
    });
}

#[test]
fn fills_absent_optional_and_repeated_cells_with_their_units() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int
          configuration
            <top>
              <k> 0 </k>
              <state multiplicity="?"> 1 </state>
              <thread multiplicity="*">
                <id> 0 </id>
              </thread>
            </top>
          rule <top>
            <k> 0 => 1 </k>
          </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("initializer").is_none()
                && Printer::new().print_term(body).contains("#token(\"1\"") =>
            {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn equal_concretized_defaults_have_distinct_destination_paths() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <top>
              <thread multiplicity="*" type="Set">
                <k> 0 </k>
              </thread>
            </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let mut definition = resolve_fresh_constants(&definition, 0).unwrap();
    let open_thread = incomplete_cell("<thread>", application("#cells", Vec::new()));
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .push(rule(
            rewrite(
                application(".Bag", Vec::new()),
                application("#cells", vec![open_thread.clone(), open_thread]),
            ),
            attributes(&[("label", json!("equal-defaults"))]),
        ));
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("equal-defaults") => Some(body),
            _ => None,
        })
        .expect("the repeated-cell insertion rule should remain");
    type DefaultDestination = (Term, Option<(Vec<u32>, u32)>);

    fn collect_defaults(term: &Term, defaults: &mut Vec<DefaultDestination>) {
        if matches!(term.unannotated(), Term::Apply { label, arguments }
            if label.name == "initKCell" && arguments.is_empty())
        {
            defaults.push((
                term.unannotated().clone(),
                term.metadata()
                    .and_then(|metadata| metadata.origin.as_deref())
                    .and_then(|origin| origin.destination.as_ref())
                    .map(|destination| (destination.path.clone(), destination.sentence_index)),
            ));
        }
        match term.unannotated() {
            Term::Rewrite { left, right } => {
                collect_defaults(left, defaults);
                collect_defaults(right, defaults);
            }
            Term::As { pattern, alias } => {
                collect_defaults(pattern, defaults);
                collect_defaults(alias, defaults);
            }
            Term::Sequence(items)
            | Term::Apply {
                arguments: items, ..
            } => {
                for item in items {
                    collect_defaults(item, defaults);
                }
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => {}
            Term::Annotated { .. } => unreachable!(),
        }
    }
    let mut defaults = Vec::new();
    collect_defaults(body, &mut defaults);

    assert_eq!(defaults.len(), 2, "{body:#?}");
    assert_eq!(defaults[0].0, defaults[1].0);
    let first = defaults[0]
        .1
        .as_ref()
        .expect("first default has a destination");
    let second = defaults[1]
        .1
        .as_ref()
        .expect("second default has a destination");
    assert_ne!(first.0, second.0);
    assert_eq!(first.1, second.1);
}

#[test]
fn preserves_repeated_cell_initializers_for_every_collection_shape() {
    for collection in ["Map", "Set", "List"] {
        for (shape, body, initial) in [
            ("parameterized", "$PGM:Int", ""),
            ("nullary", "0", " initial=\"\""),
        ] {
            let source = format!(
                r#"
                module MAIN
                  syntax Int ::= r"[0-9]+" [token]
                  configuration
                    <top>
                      <thread multiplicity="*" type="{collection}"{initial}>
                        <id> {body} </id>
                      </thread>
                    </top>
                  syntax K
                  syntax Map
                endmodule
                "#
            );
            let definition = resolve_semantic_casts(&parsed(&source));
            let definition = add_implicit_computation_cell(&definition).unwrap();
            let definition = resolve_fresh_constants(&definition, 0).unwrap();
            let transformed = concretize_cells(&definition).unwrap_or_else(|error| {
                panic!("{collection}/{shape} concretization failed: {error:?}")
            });
            let top_initializer = transformed
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .find_map(|sentence| match sentence {
                    Sentence::Rule {
                        body, attributes, ..
                    } if attributes.get("initializer").is_some()
                        && Printer::new().print_term(body).starts_with("initTopCell") =>
                    {
                        Some(Printer::new().print_term(body))
                    }
                    _ => None,
                })
                .expect("the generated top initializer should remain present");

            assert!(
                top_initializer.contains("initThreadCell"),
                "{collection}/{shape} lost its repeated-cell initializer: {top_initializer}"
            );
        }
    }
}

#[test]
fn splits_cell_fragment_variables_and_rebuilds_external_occurrences() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "isTopCellFragment" "(" TopCellFragment ")"
            [function, symbol(isTopCellFragment)]
          syntax Bool ::= "ok" "(" TopCellFragment ")" [function, symbol(ok)]
          configuration
            <top>
              <k> 0 </k>
              <state> 1 </state>
              <env> 2 </env>
            </top>
          rule <top>
            <k> 0 => 1 ... </k>
            CELLS:TopCellFragment
          </top>
          requires isTopCellFragment(CELLS)
          ensures ok(CELLS)
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes,
                ..
            } if attributes.get("initializer").is_none() => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
                Printer::new().print_term(ensures),
            )),
            _ => None,
        })
        .unwrap();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(output);
    });
}

#[test]
fn finalizes_language_parsing_and_sort_predicate_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
        endmodule
    "#};
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let definition = add_semantics_module(&definition).unwrap();
    let definition = number_sentences(&generate_sort_predicate_rules(&definition));
    let language = definition
        .modules
        .iter()
        .find(|module| module.name == "LANGUAGE-PARSING")
        .unwrap();
    assert_eq!(
        language
            .imports
            .iter()
            .map(|import| import.name.as_str())
            .collect::<Vec<_>>(),
        ["MAIN"]
    );
    let predicates = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if Printer::new().print_term(body).starts_with("isExp(") => Some((
                Printer::new().print_term(body),
                attributes.get("owise").is_some(),
                attributes.get_str("UNIQUE_ID").map(str::to_owned),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(predicates);
    });
    assert_has_generated_by(&definition, GeneratingPass::GenerateSortPredicateRules);
}

#[test]
fn marks_variable_headed_main_cell_sequences_as_cool_like() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> 0 </k>
          rule <k> REST:K ~> 0 => REST ... </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let definition = concretize_cells(&definition).unwrap();
    let definition = add_cool_like_attributes(&definition);
    let rendered = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => Some((
                Printer::new().print_term(body),
                snapshot_attributes(attributes),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(
                |sentence| matches!(sentence, Sentence::Rule { attributes, .. }
            if attributes.get("initializer").is_none()
                && attributes.get("cool-like").is_some())
            ),
        "{rendered:#?}"
    );
}

#[test]
fn marks_cool_like_rules_of_imported_modules_through_the_main_module() {
    // KoreBackend applies `new AddCoolLikeAtt(d.mainModule())` to every module's sentences, so
    // the `maincell` lookup goes through the main module's productions even for a rule declared
    // in an imported module that does not see the configuration itself (regression-new
    // equals-pattern: `rule I:Int => ...` in TEST-SYNTAX, the configuration generated in TEST).
    let source = indoc! {r#"
        module MAIN-SYNTAX
          syntax Int ::= r"[0-9]+" [token]
          syntax KItem ::= foo(Int) [symbol(foo)]
          rule I:Int => foo(I)
          rule foo(0) => 1
          syntax K
          syntax Map
        endmodule

        module MAIN
          imports MAIN-SYNTAX
          configuration <k> 0 </k>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let definition = concretize_cells(&definition).unwrap();
    let definition = add_cool_like_attributes(&definition);
    let syntax_module = definition
        .modules
        .iter()
        .find(|module| module.name == "MAIN-SYNTAX")
        .unwrap();
    let rules = syntax_module
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } => Some((
                Printer::new().print_term(body),
                attributes.get("cool-like").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    let cool_like = rules
        .iter()
        .filter(|(_, cool_like)| *cool_like)
        .map(|(body, _)| body.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        cool_like.len(),
        1,
        "exactly the variable-headed rule: {rules:#?}"
    );
    assert!(cool_like[0].contains("``I=>foo(I)``~>"), "{rules:#?}");
}

#[test]
fn strictness_bool_import_rebases_existing_production_metadata() {
    for import in ["", "imports BOOL"] {
        let source = indoc! {r#"
            module BOOL
              syntax Bool ::= "true" [symbol(true)]
            endmodule
            module MAIN
              IMPORT
              syntax Exp ::= "a" [symbol(a)]
                           | "f(" Exp ")" [strict, function, symbol(f)]
              rule f(a) => a
            endmodule
        "#}
        .replace("IMPORT", import);
        let original = parsed(&source);
        let original_resolved = ResolvedDefinition::resolve(&original).unwrap();
        let original_catalog =
            original_resolved.production_catalog(original_resolved.main_module_id());
        let transformed = resolve_strict(&original).unwrap();
        let resolved = ResolvedDefinition::resolve(&transformed).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let left = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match sentence {
                Sentence::Rule { body, .. } => match body.unannotated() {
                    Term::Rewrite { left, .. } => Some(left),
                    _ => None,
                },
                _ => None,
            })
            .unwrap();
        let id = left.metadata().unwrap().production.unwrap();
        let expected = original_catalog.productions_for(&LabelHead::new("f"))[0];
        assert_eq!(
            catalog.production(ProductionId(id.0)),
            original_catalog.production(expected),
            "strictness must retain the original production when BOOL is newly or already imported"
        );
        module_to_kore(&transformed, "MAIN").expect("rebased equation must emit");
    }
}

#[test]
fn generates_left_to_right_seqstrict_contexts_and_imports_bool() {
    let source = indoc! {r#"
        module BOOL
        endmodule

        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | Exp "+" Exp [seqstrict, symbol(_+_)]
        endmodule
    "#};
    let transformed = resolve_strict(&parsed(source)).unwrap();
    let main = transformed.main_module().unwrap();
    assert_eq!(
        main.imports
            .iter()
            .filter(|import| import.name == "BOOL" && !import.public)
            .count(),
        1
    );
    let contexts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Context {
                body,
                requires,
                attributes,
            } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
                attributes.get_str("label").map(str::to_owned),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(contexts);
    });
}

#[test]
fn strictness_contexts_link_to_their_source_production() {
    let source = indoc! {r#"
        module BOOL
        endmodule

        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | Exp "+" Exp [seqstrict, symbol(_+_)]
        endmodule
    "#};
    let strict_text = r#"Exp "+" Exp [seqstrict, symbol(_+_)]"#;
    let strict_start = source.find(strict_text).unwrap();
    let strict_span = TermSpan {
        source: SourceId(0),
        start: strict_start,
        end: strict_start + strict_text.len(),
    };

    let transformed = resolve_strict(&parsed(source)).unwrap();
    let contexts = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| matches!(sentence, Sentence::Context { .. }))
        .collect::<Vec<_>>();
    assert_eq!(contexts.len(), 2);
    for context in contexts {
        let receipt = context
            .attributes()
            .get(ORIGIN_ATTRIBUTE)
            .expect("strictness context has an origin");
        assert_eq!(receipt["pass"], GeneratingPass::ResolveStrict.as_str());
        assert_eq!(
            receipt["origins"],
            serde_json::json!([{
                "kind": "source",
                "source": strict_span.source.0,
                "start": strict_span.start,
                "end": strict_span.end,
            }]),
        );
    }
}

#[test]
fn expands_context_alias_groups_context_rewrites_and_hybrid_rules() {
    let alias = Sentence::ContextAlias {
        body: application("wrapper", vec![Term::variable("HERE")]),
        requires: application("allowed", vec![Term::variable("K0")]),
        attributes: attributes(&[
            ("label", json!("custom")),
            ("context", json!("resume")),
            ("result", json!("Foo")),
        ]),
    };
    let strict = Sentence::Production {
        label: Some(Label::new("step")),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![
            ProductionItem::NonTerminal {
                sort: Sort::new("Exp"),
                name: None,
            },
            ProductionItem::NonTerminal {
                sort: Sort::new("Exp"),
                name: None,
            },
        ],
        attributes: attributes(&[("seqstrict", json!("custom;1,2")), ("hybrid", json!("Foo"))]),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module("MAIN", vec![alias, strict]),
        ],
        attributes: Attributes::default(),
    };

    let transformed = resolve_strict(&definition).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        !main
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::ContextAlias { .. }))
    );
    let contexts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Context { body, requires, .. } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(contexts.len(), 2);
    assert!(
        contexts
            .iter()
            .all(|(body, _)| body.contains("#SemanticCastToExp(HOLE)=>resume")),
        "{contexts:#?}"
    );
    assert!(contexts[1].1.contains("isFoo(K0)"), "{contexts:#?}");
    assert!(main.local_sentences.iter().any(|sentence| {
        matches!(sentence, Sentence::Rule { body, requires, .. }
            if Printer::new().print_term(body).starts_with("isFoo(step(")
                && Printer::new().print_term(requires).contains("isFoo(K0)")
                && Printer::new().print_term(requires).contains("isFoo(K1)"))
    }));
}

#[test]
fn rejects_strictness_aliases_that_do_not_exist() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module(
                "MAIN",
                vec![Sentence::Production {
                    label: Some(Label::new("step")),
                    parameters: Vec::new(),
                    sort: Sort::new("Exp"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: Sort::new("Exp"),
                        name: None,
                    }],
                    attributes: attributes(&[("strict", json!("missing"))]),
                }],
            ),
        ],
        attributes: Attributes::default(),
    };

    let error = resolve_strict(&definition).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].message,
        "Found rule label \"missing\" in strictness attribute which did not refer to any sentence."
    );
}

#[test]
fn gives_anonymous_variables_collision_free_sentence_local_names() {
    let first = Sentence::Rule {
        body: application(
            "pair",
            vec![
                Term::variable("_Gen0"),
                Term::Variable {
                    name: "_".into(),
                    sort: Some(Sort::new("Exp")),
                },
                Term::variable("?_"),
            ],
        ),
        requires: application("needs", vec![Term::variable("!_")]),
        ensures: application("keeps", vec![Term::variable("@_")]),
        attributes: Attributes::default(),
    };
    let second = rule(
        application("other", vec![Term::variable("_")]),
        Attributes::default(),
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module("MAIN", vec![first, second])],
        attributes: Attributes::default(),
    };

    let transformed = resolve_anon_vars(&definition);
    let rendered = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            } => Some((
                Printer::new().print_term(body),
                Printer::new().print_term(requires),
                Printer::new().print_term(ensures),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        rendered[0].0.contains("_Gen0,_Gen1,?_Gen2"),
        "{rendered:#?}"
    );
    assert!(rendered[0].1.contains("!_Gen3"), "{rendered:#?}");
    assert!(rendered[0].2.contains("@_Gen4"), "{rendered:#?}");
    assert!(rendered[1].0.contains("_Gen0"), "{rendered:#?}");
    assert_generated_by(&transformed, GeneratingPass::ResolveAnonymousVariables);
}

#[test]
fn pattern01a_anonymous_sentence_reports_only_exact_minted_identities() {
    let sentence = Sentence::Rule {
        body: application(
            "body",
            vec![
                Term::variable("_Gen0"),
                Term::variable("_"),
                Term::variable("?_"),
            ],
        ),
        requires: application("requires", vec![Term::variable("!_")]),
        ensures: application("ensures", vec![Term::variable("@_")]),
        attributes: attributes(&[("label", json!("pattern"))]),
    };

    let (sentence, generated) = resolve_anon_vars_in_sentence(sentence);
    assert_eq!(
        generated,
        BTreeSet::from([
            GeneratedVariableIdentity::element("_Gen1"),
            GeneratedVariableIdentity::element("?_Gen2"),
            GeneratedVariableIdentity::element("!_Gen3"),
            GeneratedVariableIdentity::set("@_Gen4"),
        ])
    );
    assert!(!generated.contains(&GeneratedVariableIdentity::element("_Gen0")));
    let Sentence::Rule { attributes, .. } = sentence else {
        unreachable!()
    };
    assert_eq!(attributes.get_str("label"), Some("pattern"));
}

#[test]
fn pattern01a_semantic_cast_sentence_shares_sorts_across_rule_roots() {
    let sentence = Sentence::Rule {
        body: application("body", vec![Term::variable("X")]),
        requires: application("#SemanticCastToInt", vec![Term::variable("X")]),
        ensures: application("ensures", vec![Term::variable("X")]),
        attributes: Attributes::default(),
    };

    let transformed = resolve_semantic_casts_in_sentence(sentence);
    let mut sorts = Vec::new();
    if let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = transformed
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
    }
    assert_eq!(sorts, vec![Some(Sort::new("Int")); 3]);
}

#[test]
fn semantic_cast_predicates_share_sorts_across_roots_and_preserve_compound_metadata() {
    let sentence = Sentence::Rule {
        body: application(
            "body",
            vec![
                Term::variable("X"),
                application(
                    "#SemanticCastToInt",
                    vec![
                        application("choice", Vec::new()).with_metadata(TermMetadata {
                            span: Some(TermSpan {
                                source: SourceId(7),
                                start: 11,
                                end: 17,
                            }),
                            production: Some(ResolvedProductionId(3)),
                            ..TermMetadata::default()
                        }),
                    ],
                ),
            ],
        ),
        requires: application("existing", vec![Term::variable("X"), Term::variable("Y")]),
        ensures: application(
            "ensures",
            vec![
                application("#SemanticCastToInt", vec![Term::variable("X")]),
                application("#SemanticCastToBool", vec![Term::variable("Y")]),
            ],
        ),
        attributes: Attributes::default(),
    };

    let transformed = resolve_semantic_casts_with_predicates_in_sentence(sentence);
    let Sentence::Rule {
        body,
        requires,
        ensures,
        ..
    } = transformed
    else {
        unreachable!()
    };

    for root in [&body, &requires, &ensures] {
        root.visit_preorder(&mut |term| {
            if let Term::Apply { label, .. } = term.unannotated() {
                assert!(!label.name.starts_with("#SemanticCastTo"), "{term}");
            }
            if let Term::Variable { name, sort } = term.unannotated() {
                let expected = match name.as_str() {
                    "X" => Some(Sort::new("Int")),
                    "Y" => Some(Sort::new("Bool")),
                    _ => return,
                };
                assert_eq!(sort, &expected, "{term}");
            }
        });
    }

    let Term::Apply { label, arguments } = requires.unannotated() else {
        panic!("expected predicate conjunction: {requires}")
    };
    assert_eq!(label.name, "_andBool_");
    let [predicates, existing] = arguments.as_slice() else {
        panic!("expected predicates and prior requires: {requires}")
    };
    assert!(matches!(
        existing.unannotated(),
        Term::Apply { label, .. } if label.name == "existing"
    ));

    let mut predicate_labels = Vec::new();
    let mut compound_metadata = None;
    predicates.visit_preorder(&mut |term| {
        let Term::Apply { label, arguments } = term.unannotated() else {
            return;
        };
        if matches!(label.name.as_str(), "isInt" | "isBool") {
            predicate_labels.push(label.name.clone());
            if let [argument] = arguments.as_slice()
                && matches!(
                    argument.unannotated(),
                    Term::Apply { label, .. } if label.name == "choice"
                )
            {
                compound_metadata = argument.metadata().cloned();
            }
        }
        assert!(arguments.len() <= 2 || label.name != "_andBool_");
    });
    predicate_labels.sort();
    assert_eq!(predicate_labels, ["isBool", "isInt", "isInt"]);
    let compound_metadata = compound_metadata.expect("compound predicate operand has metadata");
    assert_eq!(compound_metadata.sort, Some(Sort::new("Int")));
    assert_eq!(compound_metadata.production, Some(ResolvedProductionId(3)));
    assert_eq!(
        compound_metadata.span,
        Some(TermSpan {
            source: SourceId(7),
            start: 11,
            end: 17,
        })
    );
}

#[test]
fn semantic_cast_predicates_are_suppressed_for_macro_and_alias_rules() {
    for attribute in ["macro", "macro-rec", "alias", "alias-rec"] {
        let sentence = Sentence::Rule {
            body: application("#SemanticCastToInt", vec![Term::variable("X")]),
            requires: truth(),
            ensures: truth(),
            attributes: attributes(&[(attribute, json!(""))]),
        };
        let transformed = resolve_semantic_casts_with_predicates_in_sentence(sentence);
        let Sentence::Rule { body, requires, .. } = transformed else {
            unreachable!()
        };
        assert!(matches!(
            body.unannotated(),
            Term::Variable { name, sort: Some(sort) }
                if name == "X" && sort == &Sort::new("Int")
        ));
        assert_eq!(requires, truth());
    }
}

#[test]
fn pattern01a_cell_sentence_reports_only_minted_dot_variables_and_preserves_source() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> 0 </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let open_cell = |body| {
        application(
            "<k>",
            vec![
                application("#dots", Vec::new()),
                body,
                application("#dots", Vec::new()),
            ],
        )
    };
    let int_token = || Term::Token {
        token: "0".into(),
        sort: Sort::new("Int"),
    };
    let sentence = Sentence::Rule {
        body: open_cell(Term::Sequence(vec![
            Term::variable("_DotVar0"),
            int_token(),
        ])),
        requires: open_cell(int_token()),
        ensures: open_cell(int_token()),
        attributes: attributes(&[
            ("anywhere", json!("")),
            (k_rust::definition::SOURCE_ATTRIBUTE, json!("pattern.k")),
            (k_rust::definition::LOCATION_ATTRIBUTE, json!([4, 2, 4, 30])),
        ]),
    };

    let (sentence, generated) = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap();
    assert_eq!(generated.len(), 6, "{generated:#?}");
    assert!(generated.iter().all(|identity| {
        identity.kind == k_rust::kore::ast::VariableKind::Element
            && identity.name.starts_with("_DotVar")
    }));
    assert!(!generated.contains(&GeneratedVariableIdentity::element("_DotVar0")));
    assert_eq!(sentence.attributes().source(), Some("pattern.k"));
}

#[test]
fn close_cells_parent_first_keeps_outer_placeholder_identity() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> <k> 0 </k> </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let sentence = Sentence::Rule {
        body: application(
            "<k>",
            vec![Term::Token {
                token: "0".into(),
                sort: Sort::new("Int"),
            }],
        ),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };

    let (sentence, generated) = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap();
    assert_eq!(
        generated,
        BTreeSet::from([
            GeneratedVariableIdentity::element("_DotVar0"),
            GeneratedVariableIdentity::element("_DotVar1"),
        ])
    );
    let Sentence::Rule { body, .. } = sentence else {
        unreachable!()
    };
    let mut occurring = BTreeSet::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term.unannotated()
            && name.starts_with("_DotVar")
        {
            occurring.insert(name.clone());
        }
    });
    assert_eq!(occurring, BTreeSet::from(["_DotVar0".to_owned()]));
}

#[test]
fn close_cells_parent_first_across_three_nested_parents() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <outer> <middle> <k> 0 </k> </middle> </outer>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let sentence = Sentence::Rule {
        body: application(
            "<k>",
            vec![Term::Token {
                token: "0".into(),
                sort: Sort::new("Int"),
            }],
        ),
        requires: truth(),
        ensures: truth(),
        attributes: Attributes::default(),
    };

    let (sentence, generated) = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap();
    assert_eq!(
        generated,
        BTreeSet::from([
            GeneratedVariableIdentity::element("_DotVar0"),
            GeneratedVariableIdentity::element("_DotVar1"),
            GeneratedVariableIdentity::element("_DotVar2"),
        ])
    );
    let Sentence::Rule { body, .. } = sentence else {
        unreachable!()
    };
    let mut occurring = BTreeSet::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term.unannotated()
            && name.starts_with("_DotVar")
        {
            occurring.insert(name.clone());
        }
    });
    assert_eq!(occurring, BTreeSet::from(["_DotVar0".to_owned()]));
}

#[test]
fn close_cells_parent_first_reserves_authored_dot_variable_names() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> <k> 0 </k> </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let sentence = Sentence::Rule {
        body: application(
            "<k>",
            vec![Term::Token {
                token: "0".into(),
                sort: Sort::new("Int"),
            }],
        ),
        requires: application("uses", vec![Term::variable("_DotVar0")]),
        ensures: truth(),
        attributes: Attributes::default(),
    };

    let (sentence, generated) = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap();
    assert_eq!(
        generated,
        BTreeSet::from([
            GeneratedVariableIdentity::element("_DotVar1"),
            GeneratedVariableIdentity::element("_DotVar2"),
        ])
    );
    let Sentence::Rule { body, .. } = sentence else {
        unreachable!()
    };
    let mut occurring = BTreeSet::new();
    body.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term.unannotated()
            && name.starts_with("_DotVar")
        {
            occurring.insert(name.clone());
        }
    });
    assert_eq!(occurring, BTreeSet::from(["_DotVar1".to_owned()]));
    assert!(!generated.contains(&GeneratedVariableIdentity::element("_DotVar0")));
}

#[test]
fn close_cells_parent_first_preserves_rewrite_rhs_defaults() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> <k> 0 </k> </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let open_top = || {
        application(
            "<top>",
            vec![
                application("#dots", Vec::new()),
                application("#cells", Vec::new()),
                application("#dots", Vec::new()),
            ],
        )
    };
    let sentence = Sentence::Rule {
        body: rewrite(open_top(), open_top()),
        requires: truth(),
        ensures: truth(),
        attributes: attributes(&[("anywhere", json!(""))]),
    };

    let (sentence, generated) = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap();
    assert_eq!(
        generated,
        BTreeSet::from([GeneratedVariableIdentity::element("_DotVar0")])
    );
    let Sentence::Rule { body, .. } = sentence else {
        unreachable!()
    };
    let Term::Rewrite { left, right } = body.unannotated() else {
        panic!(
            "expected a rewrite, found {}",
            Printer::new().print_term(&body)
        );
    };
    let mut left_variables = BTreeSet::new();
    left.visit_preorder(&mut |term| {
        if let Term::Variable { name, .. } = term.unannotated() {
            left_variables.insert(name.clone());
        }
    });
    let mut right_variables = BTreeSet::new();
    let mut right_labels = BTreeSet::new();
    right.visit_preorder(&mut |term| match term.unannotated() {
        Term::Variable { name, .. } => {
            right_variables.insert(name.clone());
        }
        Term::Apply { label, .. } => {
            right_labels.insert(label.name.clone());
        }
        _ => {}
    });
    assert_eq!(left_variables, BTreeSet::from(["_DotVar0".to_owned()]));
    assert!(right_variables.is_empty(), "{right_variables:#?}");
    assert!(right_labels.contains("initKCell"), "{right_labels:#?}");
}

#[test]
fn pattern01a_cell_sentence_failure_retains_original_diagnostic_source() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> 0 </k>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let sentence = Sentence::Rule {
        body: application(
            "<k>",
            vec![
                application("#dots", Vec::new()),
                Term::Token {
                    token: "0".into(),
                    sort: Sort::new("Int"),
                },
            ],
        ),
        requires: truth(),
        ensures: truth(),
        attributes: attributes(&[
            ("anywhere", json!("")),
            (k_rust::definition::SOURCE_ATTRIBUTE, json!("bad-pattern.k")),
            (k_rust::definition::LOCATION_ATTRIBUTE, json!([9, 3, 9, 17])),
        ]),
    };

    let error = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidCellConcretization
    );
    assert_eq!(
        error.diagnostics[0].source.as_deref(),
        Some("bad-pattern.k")
    );
    assert_eq!(error.diagnostics[0].location.unwrap().start_line, 9);
}

#[test]
fn lowers_contexts_to_freezer_heat_and_cool_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [symbol(f)]
          context f(HOLE)
        endmodule
    "#};
    let transformed = resolve_contexts(&resolve_anon_vars(&parsed(source))).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        !main
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Context { .. }))
    );
    let generated = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } if label.name.starts_with("#freezer") => Some(("freezer", label.name.clone(), None)),
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("heat").is_some() || attributes.get("cool").is_some() => Some((
                if attributes.get("heat").is_some() {
                    "heat"
                } else {
                    "cool"
                },
                Printer::new().print_term(body),
                attributes.get_str("label").map(str::to_owned),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(generated);
    });
}

#[test]
fn heat_and_cool_rules_carry_their_exact_context_origins() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [symbol(f)]
                       | "g(" Exp ")" [symbol(g)]
          context f(HOLE) [label(first)]
          context g(HOLE) [label(second)]
        endmodule
    "#};
    let source_span = |text: &str| {
        let start = source.find(text).unwrap();
        TermSpan {
            source: SourceId(0),
            start,
            end: start + text.len(),
        }
    };
    let first_span = source_span("f(HOLE)");
    let second_span = source_span("g(HOLE)");
    let transformed = resolve_contexts(&resolve_anon_vars(&parsed(source))).unwrap();
    let main = transformed.main_module().unwrap();
    let generated = main
        .local_sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| match sentence {
            Sentence::Production {
                label: Some(label), ..
            } => label.name.starts_with("#freezer"),
            Sentence::Rule { attributes, .. } => {
                attributes.get("heat").is_some() || attributes.get("cool").is_some()
            }
            _ => false,
        })
        .collect::<Vec<_>>();

    assert_eq!(generated.len(), 6);
    for (group, expected_span, unrelated_span) in [
        (&generated[..3], first_span, second_span),
        (&generated[3..], second_span, first_span),
    ] {
        for (sentence_index, sentence) in group {
            let receipt = sentence
                .attributes()
                .get(ORIGIN_ATTRIBUTE)
                .expect("generated context sentence has an origin");
            assert_eq!(receipt["pass"], GeneratingPass::ResolveContexts.as_str());
            let links = receipt["origins"].as_array().unwrap();
            let expected = serde_json::json!({
                "kind": "source",
                "source": expected_span.source.0,
                "start": expected_span.start,
                "end": expected_span.end,
            });
            let unrelated = serde_json::json!({
                "kind": "source",
                "source": unrelated_span.source.0,
                "start": unrelated_span.start,
                "end": unrelated_span.end,
            });
            assert!(links.contains(&expected), "{receipt}");
            assert!(!links.contains(&unrelated), "{receipt}");
            assert_eq!(receipt["destination"]["sentenceIndex"], *sentence_index);

            if let Sentence::Rule { body, .. } = sentence {
                let origin = body
                    .metadata()
                    .and_then(|metadata| metadata.origin.as_deref())
                    .expect("generated heat/cool body has an origin");
                assert_eq!(origin.pass, GeneratingPass::ResolveContexts);
                assert!(
                    origin.origins.contains(&ProvenanceLink::Source {
                        span: expected_span,
                    }),
                    "{origin:?}",
                );
                assert!(!origin.origins.contains(&ProvenanceLink::Source {
                    span: unrelated_span,
                }));
                let destination = origin.destination.as_ref().unwrap();
                assert_eq!(
                    destination.sentence_index,
                    u32::try_from(*sentence_index).unwrap()
                );
                assert_eq!(destination.path, [0]);
            }
        }
    }
}

#[test]
fn inserts_context_rewrites_inside_the_main_cell() {
    let context = Sentence::Context {
        body: incomplete_cell(
            "<k>",
            application("f", vec![Term::variable("HOLE"), Term::variable("X")]),
        ),
        requires: truth(),
        attributes: attributes(&[("label", json!("evaluate"))]),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::Production {
                    label: Some(Label::new("<k>")),
                    parameters: Vec::new(),
                    sort: Sort::new("KCell"),
                    items: vec![ProductionItem::NonTerminal {
                        sort: Sort::new("K"),
                        name: None,
                    }],
                    attributes: attributes(&[("maincell", json!(""))]),
                },
                context,
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = resolve_contexts(&definition).unwrap();
    let rules = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get("heat").is_some() || attributes.get("cool").is_some() => Some((
                Printer::new().print_term(body),
                attributes.get_str("label").unwrap().to_owned(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(rules.len(), 2);
    assert!(
        rules
            .iter()
            .all(|(body, _)| body.starts_with("`<k>`(#noDots(.KList),")),
        "{rules:#?}"
    );
    assert!(rules.iter().any(|(_, label)| label == "evaluate-heat"));
    assert!(rules.iter().any(|(_, label)| label == "evaluate-cool"));
}

#[test]
fn rejects_invalid_context_shapes() {
    let cases = [
        (
            application("f", vec![Term::variable("X")]),
            "Contexts must have at least one HOLE.",
        ),
        (
            application(
                "f",
                vec![
                    rewrite(Term::variable("HOLE"), Term::variable("X")),
                    rewrite(Term::variable("HOLE"), Term::variable("Y")),
                ],
            ),
            "Cannot compile a context with multiple rewrites.",
        ),
        (
            application(
                "f",
                vec![
                    Term::variable("HOLE"),
                    rewrite(Term::variable("X"), Term::variable("Y")),
                ],
            ),
            "Only the HOLE can be rewritten in a context definition",
        ),
    ];
    for (body, expected) in cases {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module(
                "MAIN",
                vec![Sentence::Context {
                    body,
                    requires: truth(),
                    attributes: Attributes::default(),
                }],
            )],
            attributes: Attributes::default(),
        };
        let error = resolve_contexts(&definition).unwrap_err();
        assert_eq!(error.diagnostics[0].message, expected);
    }
}

#[test]
fn reuses_lhs_subterms_on_rule_right_hand_sides() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool [hook(BOOL.Bool)]
          syntax Bool ::= r"true|false" [token]
          syntax Exp ::= "wrap(" Bool ")" [symbol(wrap)]
          rule wrap(false) => wrap(false)
          rule wrap(true) => wrap(true) [simplification]
        endmodule
    "#};
    let transformed = minimize_term_construction(&parsed(source)).unwrap();
    let rules = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .collect::<Vec<_>>();

    insta::with_settings!({
        description => format!("K definition:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(rules);
    });
    assert_generated_by(&transformed, GeneratingPass::MinimizeTermConstruction);
}

#[test]
fn alias_names_avoid_every_sort_of_an_existing_name() {
    let source = indoc! {r#"
        module MAIN
          syntax Int
          syntax Cell ::= "cell" [symbol(cell)]
          syntax Root ::= "root" "(" Cell "," Int ")" [symbol(root)]
          rule root(cell, _Gen0:Int) => root(cell, _Gen0:Int)
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let transformed = minimize_term_construction(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    let mut aliases = Vec::new();
    body.visit_preorder(&mut |term| {
        if let Term::As { alias, .. } = term
            && let Term::Variable { name, sort } = alias.unannotated()
        {
            aliases.push((name.clone(), sort.clone()));
        }
    });

    assert_eq!(aliases, [("_Gen1".into(), Some(Sort::new("Cell")))]);
}

#[test]
fn minimizes_imported_aliases_with_symbols_generated_in_the_main_module() {
    let generated_top = Sentence::Production {
        label: Some(Label::new("<generatedTop>")),
        parameters: Vec::new(),
        sort: Sort::new("GeneratedTopCell"),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("Cell"),
            name: None,
        }],
        attributes: Attributes::default(),
    };
    let top = application("<generatedTop>", vec![application("cell", Vec::new())]);
    let aliased = Term::As {
        pattern: Box::new(top.clone()),
        alias: Box::new(Term::Variable {
            name: "#Configuration".into(),
            sort: Some(Sort::new("GeneratedTopCell")),
        }),
    };
    let mut main = module("MAIN", vec![generated_top]);
    main.imports.push(FlatImport {
        name: "LIB".into(),
        public: true,
    });
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module(
                "LIB",
                vec![
                    production("cell", "Cell", Attributes::default()),
                    rule(rewrite(aliased, top), Attributes::default()),
                ],
            ),
            main,
        ],
        attributes: Attributes::default(),
    };

    let transformed = minimize_term_construction(&definition)
        .expect("main-module generated symbols should sort imported aliases");
    let rendered = transformed
        .modules
        .iter()
        .find(|module| module.name == "LIB")
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .unwrap();
    assert!(rendered.contains("_Gen"), "{rendered}");
}

#[test]
fn removes_associative_units_from_rules_only() {
    let collection_attributes = attributes(&[("assoc", json!("")), ("unit", json!(".Items"))]);
    let unit = || application(".Items", vec![]);
    let concat = |left, right| application("_Items_", vec![left, right]);
    let nested = concat(
        concat(application("a", vec![]), unit()),
        concat(unit(), application("b", vec![])),
    );
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("_Items_", "Items", collection_attributes),
                production(".Items", "Items", Attributes::default()),
                production("a", "Items", Attributes::default()),
                production("b", "Items", Attributes::default()),
                rule(rewrite(nested.clone(), nested), Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = remove_unit(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .unwrap();
    assert_eq!(
        Printer::new().print_term(body),
        "`_Items_`(a(.KList),b(.KList))=>`_Items_`(a(.KList),b(.KList))"
    );
}

#[test]
fn fabricated_collection_units_replace_spans_with_generation_origins() {
    let collection_attributes = attributes(&[("assoc", json!("")), ("unit", json!(".Items"))]);
    let span = TermSpan {
        source: SourceId(0),
        start: 10,
        end: 30,
    };
    let body = application(
        "_Items_",
        vec![
            application(".Items", Vec::new()),
            application(".Items", Vec::new()),
        ],
    )
    .with_metadata(TermMetadata {
        span: Some(span),
        ..TermMetadata::default()
    });
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("_Items_", "Items", collection_attributes),
                production(".Items", "Items", Attributes::default()),
                rule(body, Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = remove_unit(&definition).unwrap();
    let body = match &transformed.main_module().unwrap().local_sentences[2] {
        Sentence::Rule { body, .. } => body,
        _ => panic!("expected a rule"),
    };
    assert!(
        matches!(body.unannotated(), Term::Apply { label, arguments }
        if label.name == ".Items" && arguments.is_empty())
    );
    let metadata = body
        .metadata()
        .expect("fabricated unit should carry provenance");
    assert_eq!(metadata.span, None);
    let origin = metadata
        .origin
        .as_deref()
        .expect("fabricated unit has an origin");
    assert_eq!(origin.pass, GeneratingPass::RemoveUnit);
    assert_eq!(origin.origins.as_ref(), [ProvenanceLink::Source { span }]);
}

#[test]
fn preserves_optional_cell_units() {
    let attributes = attributes(&[
        ("assoc", json!("")),
        ("unit", json!("noCell")),
        ("cell", json!("")),
        ("multiplicity", json!("?")),
    ]);
    let body = application("cells", vec![application("noCell", vec![])]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("cells", "Cell", attributes),
                rule(body.clone(), Attributes::default()),
            ],
        )],
        attributes: Attributes::default(),
    };

    let transformed = remove_unit(&definition).unwrap();
    let preserved = transformed.main_module().unwrap().local_sentences[1].clone();
    assert!(matches!(preserved, Sentence::Rule { body: actual, .. } if actual == body));
}

#[test]
fn validates_smt_lemmas_after_expanding_aliases() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | "pow256" [alias, symbol(pow256)]
                       | "chop" "(" Int ")" [function, total, smtlib(chop), symbol(chop)]
                       | Int "mod" Int [function, total, smt-hook(mod), symbol(mod)]
          rule pow256 => 256
          rule chop(I:Int) => I mod pow256 [smt-lemma]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    assert!(
        check_definition(&resolved).unwrap().iter().all(
            |diagnostic| diagnostic.code != k_rust::diagnostic::DiagnosticCode::InvalidSmtLemma
        )
    );

    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let smt_lemma = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| sentence.attributes().get("smt-lemma").is_some())
        .unwrap();
    let Sentence::Rule { body, .. } = smt_lemma else {
        panic!("expected an SMT lemma rule");
    };
    assert!(!Printer::new().print_term(body).contains("pow256"));
}

#[test]
fn language_parsing_module_preserves_imported_overload_identity() {
    // LATE reaches Y before MAIN in the original graph. LANGUAGE-PARSING reaches MAIN
    // earlier and visits X before Y, shifting the catalogs of MAIN and its imported owner.
    let original = parsed(indoc! {r#"
        module X
          syntax X ::= "x" [symbol(x)]
          syntax X ::= "fx(" X ")" [function, symbol(f)]
        endmodule
        module Y
          syntax Y ::= "y" [symbol(y)]
          syntax Y ::= "fy(" Y ")" [function, symbol(f)]
        endmodule
        module OWNER
          imports X
          imports Y
          rule fx(x) => x
        endmodule
        module LEFT
          imports OWNER
        endmodule
        module RIGHT
          imports OWNER
        endmodule
        module LATE
          imports Y
        endmodule
        module MAIN
          imports LEFT
          imports RIGHT
          rule fy(y) => y
        endmodule
    "#});
    let before = ResolvedDefinition::resolve(&original).unwrap();
    let transformed = add_semantics_module(&original).unwrap();
    let after = ResolvedDefinition::resolve(&transformed).unwrap();
    for owner in ["OWNER", "MAIN"] {
        let before_id = before.module_id(owner).unwrap();
        let after_id = after.module_id(owner).unwrap();
        let source = before.production_catalog(before_id);
        let target = after.production_catalog(after_id);
        let rule_head = |module: &k_rust::definition::ResolvedModule| {
            module
                .local_sentences
                .iter()
                .find_map(|sentence| {
                    let Sentence::Rule { body, .. } = sentence else {
                        return None;
                    };
                    let Term::Rewrite { left, .. } = body.unannotated() else {
                        return None;
                    };
                    left.metadata().cloned()
                })
                .unwrap()
        };
        let mut original_metadata = rule_head(before.module(before_id));
        let rebased_metadata = rule_head(after.module(after_id));
        let old_index = original_metadata.production.unwrap();
        let new_index = rebased_metadata.production.unwrap();
        let expected = source.production(ProductionId(old_index.0));
        assert_ne!(
            target.production(ProductionId(old_index.0)),
            expected,
            "fixture must shift the original catalog position for {owner}"
        );
        assert_eq!(
            target.production(ProductionId(new_index.0)),
            expected,
            "{owner}: preserve the selected argument/result-sort overload and its provenance"
        );
        original_metadata.production = rebased_metadata.production;
        assert_eq!(original_metadata, rebased_metadata);
    }
    module_to_kore(&transformed, "MAIN").expect("local and imported equations must emit");
    assert_eq!(add_semantics_module(&transformed).unwrap(), transformed);
}

#[test]
fn rebuilds_cell_fragments_used_as_data_inside_leaf_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax KItem ::= "save" "(" TopCellFragment ")" [symbol(save)]
          configuration <top> <k> .K </k> <state> 0 </state> </top>
          rule <top> <k> save(C) => .K </k> C:TopCellFragment </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source));
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let (body, requires) = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule {
                body,
                requires,
                attributes,
                ..
            } if attributes.get("initializer").is_none() => Some((body, requires)),
            _ => None,
        })
        .unwrap();
    let mut variable_sorts = Vec::new();
    let mut saved_fragments = 0;
    for term in [body, requires] {
        term.visit_preorder(&mut |term| {
            if let Term::Variable { name, sort } = term
                && name == "C"
            {
                variable_sorts.push(sort.clone());
            }
            if let Term::Apply { label, arguments } = term
                && label.name == "save"
            {
                let Term::Apply { label, .. } = arguments[0].unannotated() else {
                    panic!("the saved value must reconstruct the original fragment: {term}");
                };
                assert_eq!(label.name, "<top>-fragment");
                saved_fragments += 1;
            }
        });
    }
    assert_eq!(saved_fragments, 1);
    assert!(variable_sorts.len() >= 2);
    assert!(
        variable_sorts
            .iter()
            .all(|sort| sort.as_ref() == Some(&Sort::new("StateCell"))),
        "{variable_sorts:?}"
    );
}
