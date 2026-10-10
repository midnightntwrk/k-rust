// The embedded standard prelude loads in the portable build to the same definition as in the
// z3-inference build (inner_rules::the_standard_prelude_loads_to_the_same_definition_in_both_builds).
// Fixtures gated on `z3-inference` below are gated for their own rules or pinned results, not for
// the prelude: parametric sort inference, an ambiguous forest outside the portable decision, or
// an assertion not yet checked against the portable build.

use indoc::indoc;
#[cfg(feature = "z3-inference")]
use k_rust::definition::AttributeKey;
#[cfg(feature = "z3-inference")]
use k_rust::kore::{
    ast::{Pattern as KorePattern, Sentence as KoreSentence},
    parser::{parse_definition, parse_pattern},
};
use k_rust::{
    builtin::embedded,
    kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
    outer::{LoadOptions, load_with_options},
};
use k_rust::{
    definition::{
        Attributes, Definition, FlatImport, FlatModule, LabelHead, ProductionItem,
        ResolvedDefinition, SENTENCE_END_OFFSET_ATTRIBUTE, SENTENCE_START_OFFSET_ATTRIBUTE,
        Sentence, checks::check_definition,
    },
    inner::ParsedProgram,
    kast::{Label, ProductionIdentity, Sort, Term, TermMetadata, TermSpan, printer::Printer},
    kompile::{
        GeneratedVariableIdentity, MacroExpansionDefinition, add_cool_like_attributes,
        add_implicit_computation_cell, add_semantics_module, add_sort_injections_to_definition,
        check_simplification_rules, concretize_cells, concretize_cells_in_sentence, constant_fold,
        expand_macros, expand_macros_in_term, generate_sort_predicate_rules,
        generate_sort_predicate_syntax, generate_sort_projections, guard_or_patterns,
        minimize_term_construction, module_to_kore, number_sentences, propagate_macro_attributes,
        remove_unit, resolve_anon_vars, resolve_anon_vars_in_sentence, resolve_comm,
        resolve_config_var, resolve_contexts, resolve_fresh_config_constants,
        resolve_fresh_constants, resolve_fun, resolve_function_with_config,
        resolve_heat_cool_attributes, resolve_io, resolve_semantic_casts,
        resolve_semantic_casts_in_sentence, resolve_semantic_casts_with_predicates_in_sentence,
        resolve_strict, subsort_kitem, term_to_kore,
    },
    outer::{ResolvedSource, load},
    provenance::{
        GeneratingPass, INPUT_ADDRESSES_ATTRIBUTE, InputAddress, InputSpace, ORIGIN_ATTRIBUTE,
        ProvenanceLink, SourceId,
    },
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
    .into_definition()
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
                Some(value.as_utf8().unwrap().to_owned())
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
    // The issue-1573 regression: the UNIQUE_ID digest hashes the rule as the parser completed
    // it, so the UNIQUE_ID of `<v> 1 => foo(1) </v>` (line 24) records whether empty-list
    // insertion instantiated the `#KRewrite` at lub(Int, Int) and wrapped the whole rewrite in one
    // IntList singleton (the recorded identifier) or wrapped each side separately. Lines 21 and
    // 27 are the variable and list-side controls.
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

/// Load a reference fixture with the embedded prelude.
#[cfg(feature = "z3-inference")]
fn load_fixture(
    file_name: &str,
    source: &str,
    main_module: &str,
) -> k_rust::outer::LoadedDefinition {
    let prelude = embedded("prelude.md").expect("embedded prelude should exist");
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
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
    .expect("reference fixture should load")
}

/// Compile a reference fixture through the whole kompile pipeline.
#[cfg(feature = "z3-inference")]
fn compile_fixture(
    file_name: &str,
    source: &str,
    main_module: &str,
) -> k_rust::kompile::CompiledKoreArtifacts {
    let loaded = load_fixture(file_name, source, main_module);
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
    // A bare configuration variable's inferred K cast determines the cell content sort;
    // an explicit Int cast must instead select the Int projection. These casts are present
    // in the initializer body when its UNIQUE_ID is assigned. Boxed transport deliberately
    // changes a map-reading body, so pin that exact body before cast elimination rather than
    // its old item-transport hash. Initializers with no lookup retain their oracle IDs.
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
        let loaded = load_fixture(file_name, source, main_module);
        let expanded = k_rust::definition::expand_configurations(loaded.definition())
            .expect("fixture configurations should expand");
        let map_readers = expanded
            .modules
            .iter()
            .find(|module| module.name == main_module)
            .expect("fixture main module")
            .local_sentences
            .iter()
            .filter_map(|sentence| {
                let Sentence::Rule {
                    body, attributes, ..
                } = &**sentence
                else {
                    return None;
                };
                if !attributes.has(AttributeKey::Initializer) {
                    return None;
                }
                let mut reads_map = false;
                body.visit_preorder(&mut |term| {
                    reads_map |= matches!(term.unannotated(), Term::Apply { label, .. }
                        if label.name == "Map:lookup");
                });
                if !reads_map {
                    return None;
                }
                let Term::Rewrite { left, .. } = body.unannotated() else {
                    panic!("initializer must be a rewrite: {body:?}");
                };
                let Term::Apply { label, .. } = left.unannotated() else {
                    panic!("initializer left side must be an application: {left:?}");
                };
                Some((label.name.clone(), Printer::new().print_term(body)))
            })
            .collect::<BTreeMap<_, _>>();
        let mut expected_map_readers = BTreeMap::from([
            (
                "initKCell".to_owned(),
                r#"initKCell(Init)=>`<k>`(#noDots(.KList),#SemanticCastToK(`project:K`(#unboxKConfigValue(`Map:lookup`(Init,#token("$PGM","KConfigVar"))))),#noDots(.KList))"#.to_owned(),
            ),
            (
                "initNCell".to_owned(),
                r#"initNCell(Init)=>`<n>`(#noDots(.KList),#SemanticCastToInt(`project:Int`(#unboxKConfigValue(`Map:lookup`(Init,#token("$N","KConfigVar"))))),#noDots(.KList))"#.to_owned(),
            ),
        ]);
        if file_name == "test-bare-cell.k" {
            expected_map_readers.insert(
                "initPCell".to_owned(),
                r#"initPCell(Init)=>`<p>`(#noDots(.KList),#SemanticCastToK(`project:K`(#unboxKConfigValue(`Map:lookup`(Init,#token("$P","KConfigVar"))))),#noDots(.KList))"#.to_owned(),
            );
        }
        assert_eq!(
            map_readers, expected_map_readers,
            "{file_name}: exact map-reading initializer bodies before cast elimination"
        );
        let artifacts = compile_loaded_definition(&loaded, CompileOptions::default())
            .expect("reference fixture should compile");
        let actual = initializer_ids(&artifacts.definition_kore);
        let expected = oracle
            .initializer
            .iter()
            .filter(|row| row.file == file_name)
            .map(|row| (row.label.clone(), row.unique_id.clone()))
            .collect::<BTreeMap<_, _>>();
        assert!(!expected.is_empty(), "{file_name} has oracle rows");
        for (label, unique_id) in &expected {
            if map_readers.contains_key(label) {
                assert!(actual.contains_key(label), "{file_name}: emitted {label}");
                continue;
            }
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
            .map(|row| {
                // The bare PGM/P variables have an inferred K cast, now recovered from
                // project:K. The old KItem declaration reflected only the transport slot.
                let sort = match (row.name.as_str(), row.sort.as_str()) {
                    ("PGM" | "P", "KItem") => "K",
                    _ => &row.sort,
                };
                (row.name.clone(), Sort::new(sort))
            })
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
                    [KorePattern::String(value)] => Some(value.as_utf8().unwrap().to_owned()),
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
            } = &**sentence
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
            } = &**sentence
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
                    | INPUT_ADDRESSES_ATTRIBUTE
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
            } = &**sentence
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
        .filter(|(_, sentence)| matches!(&***sentence, Sentence::Rule { .. }))
        .collect::<Vec<_>>();

    assert_eq!(rules.len(), 2);
    for (sentence_index, sentence) in rules {
        let receipt = sentence.attributes().get(ORIGIN_ATTRIBUTE).unwrap();
        assert_eq!(receipt["pass"], GeneratingPass::ResolveComm.as_str());
        assert_eq!(
            receipt["destination"]["sentenceIndex"],
            serde_json::json!(sentence_index),
        );
        let Sentence::Rule { body, .. } = &**sentence else {
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
        local_sentences: sentences.into_iter().map(std::sync::Arc::new).collect(),
        attributes: Attributes::default(),
    }
}

fn semantic_cast_sentence_subsorts() -> k_rust::definition::PartialOrder<Sort> {
    let resolved = ResolvedDefinition::resolve(&Definition {
        main_module: "MAIN".into(),
        modules: vec![module("MAIN", Vec::new())],
        attributes: Attributes::default(),
    })
    .unwrap();
    resolved
        .subsorts(resolved.module_id("MAIN").unwrap())
        .unwrap()
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
        .push(production("ioHelper", "KItem", Attributes::default()).into());
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
    let Sentence::Rule { body, .. } = k_rust::definition::sentence_mut(consume) else {
        unreachable!()
    };
    let taken = std::mem::replace(body, Term::Sequence(Vec::new()));
    *body = taken.with_metadata(TermMetadata {
        production: Some(catalog.identity(cell)),
        ..TermMetadata::default()
    });

    let definition = resolve_io(&input).unwrap();
    let main = definition.main_module().unwrap();
    let rendered = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        matches!(&**sentence, Sentence::Production { sort, .. } if sort.name == "Stream")
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
    let Sentence::Rule { body, .. } = &**consume else {
        unreachable!()
    };
    let rebased = body
        .metadata()
        .and_then(|metadata| metadata.production)
        .unwrap();
    assert!(matches!(
        catalog.production(catalog.lookup(&rebased).unwrap()),
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
        .filter_map(|sentence| match &**sentence {
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
    } = k_rust::definition::sentence_mut(consume)
    else {
        unreachable!()
    };
    *body = Term::Sequence(vec![body.clone(), body.clone()]);
    *rule_attributes = attributes(&[
        ("label", json!("consume")),
        ("org.kframework.attributes.Source", json!("stdin-rule.k")),
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
    assert_eq!(diagnostic.source.as_deref(), Some("stdin-rule.k"));
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
            // The cast and Int argument make the parameter Int, covered by X:Int.
            application("#SemanticCastToInt", vec![x.clone()]),
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
        .find_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
            .any(|body| { body.contains("`#lambda__`(#SemanticCastToInt(X),Y)=>plus(X,Y)") })
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
        .filter_map(|sentence| match &**sentence {
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
        let Sentence::Rule { body, .. } = &**sentence else {
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
        .filter_map(|sentence| match &**sentence {
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
        let Sentence::Rule { body, .. } = &**sentence else {
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
        .find_map(|sentence| match &**sentence {
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
        let Sentence::Rule { body, .. } = &**sentence else {
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
        .find_map(|sentence| match &**sentence {
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
    assert!(
        lambda_attributes.get("total").is_none(),
        "the X:Item pattern leaves the K parameter's non-Item arguments without a value"
    );
}

/// `total` on a generated lambda claims that every application denotes one value, and its only
/// equation equates the application with the body; so the claim holds only when the body is
/// defined for every value of its variables. `div(Y, Y)` of a partial `div` is not, so a lambda
/// over it is a partial function, and so is every lambda whose body applies such a lambda.
#[test]
fn declares_a_generated_lambda_total_only_when_its_body_is_defined() {
    let int = || Some(Sort::new("Int"));
    let y = || Term::Variable {
        name: "Y".into(),
        sort: int(),
    };
    // `#let Y = <hint> #in <body>`: the argument variable names the lambda `#lambda<hint>__`.
    let binder = |hint: &str, body: Term| {
        application(
            "#let",
            vec![
                // The cast covers the Int parameter, so the body alone decides totality.
                application("#SemanticCastToInt", vec![y()]),
                Term::Variable {
                    name: hint.into(),
                    sort: int(),
                },
                body,
            ],
        )
    };
    let int_production = |label: &str, attributes: Attributes| Sentence::Production {
        label: Some(Label::new(label)),
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
        attributes,
    };
    let x = || Term::Variable {
        name: "X".into(),
        sort: int(),
    };
    let div = |term: Term| application("div", vec![term.clone(), term]);
    let cases = [
        ("Add", application("add", vec![y(), y()]), true),
        ("Pair", application("pair", vec![y(), y()]), true),
        ("Div", div(y()), false),
        ("Nested", application("pair", vec![y(), div(y())]), false),
        // A macro production with no expansion equation builds values (a Free head).
        ("Macro", application("twice", vec![y(), y()]), true),
        ("Wrapped", application("wrapped", vec![y(), y()]), false),
        ("Plus", application("plus", vec![y(), y()]), true),
        (
            "Unknown",
            application("pair", vec![y(), application("undeclared", vec![y()])]),
            false,
        ),
        (
            "Bottom",
            application("pair", vec![y(), application("#Bottom", Vec::new())]),
            false,
        ),
        (
            "OuterTotal",
            binder("InnerTotal", application("add", vec![y(), y()])),
            true,
        ),
        ("OuterPartial", binder("InnerPartial", div(y())), false),
    ];
    let mut sentences = vec![
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Int"),
            attributes: Attributes::default(),
        },
        int_production(
            "add",
            attributes(&[("function", json!("")), ("total", json!(""))]),
        ),
        int_production("div", attributes(&[("function", json!(""))])),
        int_production("pair", Attributes::default()),
        int_production("twice", attributes(&[("macro", json!(""))])),
        int_production("wrapped", Attributes::default()),
        int_production("plus", Attributes::default()),
        rule(
            Term::Rewrite {
                left: Box::new(application("wrapped", vec![x(), y()])),
                right: Box::new(application("div", vec![x(), y()])),
            },
            attributes(&[("anywhere", json!(""))]),
        ),
        rule(
            Term::Rewrite {
                left: Box::new(application("plus", vec![x(), y()])),
                right: Box::new(application("add", vec![x(), y()])),
            },
            attributes(&[("anywhere", json!(""))]),
        ),
    ];
    for (hint, body, _) in &cases {
        sentences.push(rule(binder(hint, body.clone()), Attributes::default()));
    }
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module("MAIN", sentences)],
        attributes: Attributes::default(),
    };

    let transformed = resolve_fun(&definition).unwrap();
    let declared_total = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name.starts_with("#lambda") => {
                Some((label.name.clone(), attributes.get("total").is_some()))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let expected = cases
        .iter()
        .map(|(hint, _, total)| (format!("#lambda{hint}__"), *total))
        .chain([
            ("#lambdaInnerTotal__".to_owned(), true),
            ("#lambdaInnerPartial__".to_owned(), false),
        ])
        .collect::<BTreeMap<_, _>>();
    assert_eq!(declared_total, expected);
}

/// A partial function whose only rule is an unconditional equation over distinct variables of
/// its declared argument sorts, with a right-hand side defined by declared attributes, has one
/// value on every argument; a lambda that applies it is total. Any other equation shape leaves
/// the function's definedness unknown, and the lambda partial.
#[test]
fn a_lambda_over_a_function_its_equation_defines_everywhere_is_total() {
    let int = || Some(Sort::new("Int"));
    let variable = |name: &str| Term::Variable {
        name: name.into(),
        sort: int(),
    };
    let token = |value: &str| Term::Token {
        token: value.into(),
        sort: Sort::new("Int"),
    };
    let function = |label: &str, arity: usize| Sentence::Production {
        label: Some(Label::new(label)),
        parameters: Vec::new(),
        sort: Sort::new("Int"),
        items: (0..arity)
            .map(|_| ProductionItem::NonTerminal {
                sort: Sort::new("Int"),
                name: None,
            })
            .collect(),
        attributes: attributes(&[("function", json!(""))]),
    };
    let equation = |label: &str, arguments: Vec<Term>, right: Term| {
        rule(
            rewrite(application(label, arguments), right),
            Attributes::default(),
        )
    };
    // (label, arity, its rules, whether the equation defines it everywhere)
    let cases: Vec<(&str, usize, Vec<Sentence>, bool)> = vec![
        (
            "constant",
            0,
            vec![equation("constant", vec![], token("1"))],
            true,
        ),
        (
            "project",
            2,
            vec![equation(
                "project",
                vec![variable("X"), Term::variable("_")],
                variable("X"),
            )],
            true,
        ),
        (
            "cast",
            1,
            vec![equation(
                "cast",
                vec![application("#SemanticCastToInt", vec![Term::variable("X")])],
                Term::variable("X"),
            )],
            true,
        ),
        (
            "lemma",
            1,
            vec![
                equation("lemma", vec![variable("X")], variable("X")),
                rule(
                    rewrite(application("lemma", vec![token("0")]), token("0")),
                    attributes(&[("simplification", json!(""))]),
                ),
            ],
            true,
        ),
        (
            "second",
            1,
            vec![
                equation("second", vec![variable("X")], variable("X")),
                equation("second", vec![token("0")], token("0")),
            ],
            false,
        ),
        (
            "conditional",
            1,
            vec![Sentence::Rule {
                body: rewrite(
                    application("conditional", vec![variable("X")]),
                    variable("X"),
                ),
                requires: application("positive", vec![variable("X")]),
                ensures: truth(),
                attributes: Attributes::default(),
            }],
            false,
        ),
        (
            "fallback",
            1,
            vec![rule(
                rewrite(application("fallback", vec![variable("X")]), variable("X")),
                attributes(&[("owise", json!(""))]),
            )],
            false,
        ),
        (
            "narrow",
            1,
            vec![equation("narrow", vec![token("1")], token("1"))],
            false,
        ),
        (
            "nonlinear",
            2,
            vec![equation(
                "nonlinear",
                vec![variable("X"), variable("X")],
                variable("X"),
            )],
            false,
        ),
        (
            "subsorted",
            1,
            vec![equation(
                "subsorted",
                vec![Term::Variable {
                    name: "X".into(),
                    sort: Some(Sort::new("Nat")),
                }],
                token("0"),
            )],
            false,
        ),
        (
            "undefined",
            1,
            vec![equation(
                "undefined",
                vec![variable("X")],
                application("div", vec![variable("X"), variable("X")]),
            )],
            false,
        ),
        // A second equation in a module MAIN does not see (EXTRA, below).
        (
            "hidden",
            1,
            vec![equation("hidden", vec![variable("X")], variable("X"))],
            false,
        ),
        (
            "recursive",
            1,
            vec![equation(
                "recursive",
                vec![variable("X")],
                application("recursive", vec![variable("X")]),
            )],
            false,
        ),
    ];
    let mut sentences = vec![
        Sentence::SyntaxSort {
            parameters: Vec::new(),
            sort: Sort::new("Int"),
            attributes: Attributes::default(),
        },
        function("div", 2),
        function("positive", 1),
    ];
    for (label, arity, rules, _) in &cases {
        sentences.push(function(label, *arity));
        sentences.extend(rules.iter().cloned());
        // `#let Y = <Label> #in label(Y, ..)`: the argument variable names the lambda.
        let hint = format!("{}{}", label[..1].to_uppercase(), &label[1..]);
        sentences.push(rule(
            application(
                "#let",
                vec![
                    // The cast covers the Int parameter, so the body alone decides totality.
                    application("#SemanticCastToInt", vec![variable("Y")]),
                    variable(&hint),
                    application(label, (0..*arity).map(|_| variable("Y")).collect()),
                ],
            ),
            Attributes::default(),
        ));
    }
    let extra = FlatModule {
        name: "EXTRA".into(),
        imports: vec![FlatImport {
            name: "MAIN".into(),
            public: true,
        }],
        local_sentences: vec![equation("hidden", vec![token("0")], token("0")).into()],
        attributes: Attributes::default(),
    };
    let definition = Definition {
        main_module: "EXTRA".into(),
        modules: vec![module("MAIN", sentences), extra],
        attributes: Attributes::default(),
    };

    let transformed = resolve_fun(&definition).unwrap();
    let declared_total = transformed
        .modules
        .iter()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name.starts_with("#lambda") => {
                Some((label.name.clone(), attributes.get("total").is_some()))
            }
            _ => None,
        })
        .collect::<BTreeMap<_, _>>();
    let expected = cases
        .iter()
        .map(|(label, _, _, total)| {
            (
                format!("#lambda{}{}__", label[..1].to_uppercase(), &label[1..]),
                *total,
            )
        })
        .collect::<BTreeMap<_, _>>();
    assert_eq!(declared_total, expected);
}

/// A function whose equation also matches the configuration (`[[ .. ]] <c> V </c>`) is defined
/// everywhere only when every configuration has exactly one `<c>`: not under a `*` cell, and not
/// when `<c>` is optional.
#[cfg(feature = "z3-inference")]
#[test]
fn a_configuration_equation_defines_its_function_only_over_a_cell_every_configuration_has() {
    let source = indoc! {r#"
        module MAIN
          imports INT
          imports MAP
          configuration <k> $PGM:K </k>
                        <one> .Map </one>
                        <many> <item multiplicity="*" type="Set"> 0 </item> </many>
                        <maybe multiplicity="?"> 0 </maybe>
          syntax Int ::= fromOne() [function] | fromItem() [function] | fromMaybe() [function]
          rule [[ fromOne() => 0 ]] <one> _M </one>
          rule [[ fromItem() => 0 ]] <item> _I </item>
          rule [[ fromMaybe() => 0 ]] <maybe> _I </maybe>
          syntax Int ::= useOne(Int) [function] | useItem(Int) [function] | useMaybe(Int) [function]
          rule useOne(One) => #fun(_O => fromOne())(One)
          rule useItem(Item) => #fun(_T => fromItem())(Item)
          rule useMaybe(Maybe) => #fun(_Y => fromMaybe())(Maybe)
        endmodule
    "#};
    let compiled = compile_fixture("config-equation.k", source, "MAIN");
    let definition = parse_definition(&compiled.definition_kore).unwrap();
    let functional = |hint: &str| {
        let name = format!("Lbl'Hash'lambda{hint}'UndsUnds'");
        definition
            .modules
            .iter()
            .flat_map(|module| &module.sentences)
            .find_map(|sentence| match sentence {
                KoreSentence::SymbolDeclaration {
                    symbol, attributes, ..
                } if symbol.name == name => Some(format!("{attributes:?}").contains("functional")),
                _ => None,
            })
            .unwrap_or_else(|| panic!("no {name} in the emitted definition"))
    };
    assert!(
        functional("One"),
        "fromOne reads a cell every configuration has"
    );
    assert_eq!(
        [functional("Item"), functional("Maybe")],
        [false, false],
        "fromItem and fromMaybe read cells some configurations lack"
    );
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
                local_sentences: vec![
                    syntax().into(),
                    rule(local_function(), Attributes::default()).into(),
                ],
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
        .filter_map(|sentence| match &**sentence {
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
        // The negated match is a `Bool` formula, so its module is given `BOOL`.
        modules: vec![
            module(
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
            ),
            module("BOOL", Vec::new()),
        ],
        attributes: Attributes::default(),
    };

    let resolved = resolve_fun(&definition).unwrap();
    let sentences = &resolved.main_module().unwrap().local_sentences;
    assert!(sentences.iter().any(|sentence| {
        matches!(&**sentence, Sentence::Rule { attributes, .. } if attributes.get("owise").is_some())
    }));
    let rendered = sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
    let transformed = resolve_semantic_casts(&transformed).unwrap();

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
            &**sentence,
            Sentence::SyntaxSort { sort, .. } if sort == &Sort::new("GeneratedTopCell")
        )),
        "adding configuration arguments must also declare GeneratedTopCell"
    );
    let production_arities = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
            .filter_map(|sentence| match &**sentence {
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
fn anywhere_macro_like_rules_are_not_anywhere_rules_for_with_config() {
    // `compute_with_config_functions` collects the head labels of the module's non-macro
    // `anywhere` rules as dependency targets, mirroring K's
    // `ComputeTransitiveFunctionDependencies`. A rule carrying `anywhere` together with any
    // macro-like key is a macro, not an `anywhere` rule. `helper` is a constructor here, so
    // its rule reaches the pass only through that set: the configuration `reader` needs must
    // not be threaded to `caller` through a macro-like `anywhere` rule.
    for macro_kind in ["macro", "macro-rec", "alias", "alias-rec"] {
        let function = attributes(&[("function", json!(""))]);
        let helper_attributes = attributes(&[("anywhere", json!("")), (macro_kind, json!(""))]);
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![module(
                "MAIN",
                vec![
                    production("reader", "Int", function.clone()),
                    production("helper", "Int", Attributes::default()),
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
            .filter_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label),
                    items,
                    ..
                } => Some((label.name.as_str(), items.len())),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(arities["reader"], 1, "{macro_kind}");
        assert_eq!(arities["helper"], 0, "{macro_kind}");
        assert_eq!(arities["caller"], 0, "{macro_kind}");
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
        .map(|id| productions.production(productions.lookup(&id).unwrap()))
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
        module BOOL
        endmodule
        module MAIN
          syntax KResult
          syntax Exp ::= heat(Exp) [symbol(heat)]
                       | cool(Exp) [symbol(cool)]
          rule heat(HOLE) => cool(HOLE) [heat, result(KResult)]
          rule cool(HOLE) => heat(HOLE) [cool, result(KResult)]
        endmodule
    "#};
    let transformed = resolve_heat_cool_attributes(&parsed(source)).unwrap();
    let requires = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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

/// A heat or cool condition is a `Bool` formula built from `BOOL`'s connectives, so the module
/// stating the rule is given a private `BOOL` import; a definition without `BOOL` is told so at
/// the rule.
#[test]
fn heat_cool_imports_bool_for_its_condition_or_reports_its_absence() {
    let main = indoc! {r#"
        module MAIN
          syntax KResult
          syntax Exp ::= heat(Exp) [symbol(heat)]
          rule heat(HOLE) => heat(HOLE) [heat, result(KResult)]
        endmodule
    "#};
    let transformed =
        resolve_heat_cool_attributes(&parsed(&format!("module BOOL\nendmodule\n{main}"))).unwrap();
    assert_eq!(
        transformed.main_module().unwrap().imports,
        [FlatImport {
            name: "BOOL".into(),
            public: false,
        }]
    );

    let error = resolve_heat_cool_attributes(&parsed(main)).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1, "{:?}", error.diagnostics);
    let diagnostic = &error.diagnostics[0];
    assert_eq!(
        diagnostic.code,
        k_rust::diagnostic::DiagnosticCode::InvalidHeatCool
    );
    assert!(
        diagnostic.message.contains("needs the module BOOL"),
        "{}",
        diagnostic.message
    );
    assert_eq!(
        diagnostic.location.map(|location| location.start_line),
        Some(4)
    );
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
            transformed
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .map(|s| &**s)
                .collect::<Vec<_>>(),
            sentences.iter().collect::<Vec<_>>()
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

/// A declared result sort whose role has no sort predicate (a numeral, a `#` sort) has no K
/// terms, so `isS` is never declared for it and no strict argument can cool to it; the result
/// predicate lookup reads the same role predicate as the generator. A defined sort is the control.
#[test]
fn heat_cool_rejects_a_declared_result_sort_without_a_sort_predicate() {
    let source = indoc! {r#"
        module BOOL
        endmodule
        module MAIN
          syntax 8
          syntax #Foo ::= "foo"
          syntax Val ::= "v"
          syntax Exp ::= heat(Exp) [symbol(heat)]
                       | cool(Exp) [symbol(cool)]
          rule heat(HOLE) => cool(HOLE) [heat, result(8)]
          rule cool(HOLE) => heat(HOLE) [cool, result(#Foo)]
          rule heat(HOLE) => heat(HOLE) [heat, result(Val)]
        endmodule
    "#};
    let error = resolve_heat_cool_attributes(&parsed(source)).unwrap_err();
    let messages = error
        .diagnostics
        .iter()
        .map(|diagnostic| {
            assert_eq!(
                diagnostic.code,
                k_rust::diagnostic::DiagnosticCode::InvalidHeatCool
            );
            diagnostic.message.clone()
        })
        .collect::<Vec<_>>();
    assert_eq!(messages.len(), 2, "{messages:?}");
    // Diagnostic sorting orders the two missing-predicate messages by their text.
    assert!(
        messages[0].starts_with(
            "Definition is missing function is#Foo required for strictness. Sort #Foo has no sort predicate"
        ),
        "{messages:?}"
    );
    assert!(
        messages[1].starts_with(
            "Definition is missing function is8 required for strictness. Sort 8 has no sort predicate"
        ),
        "{messages:?}"
    );
}

/// Through the whole pipeline, `[strict, result(8)]` is rejected by the heat/cool stage with the
/// `InvalidHeatCool` diagnostic, before any later stage looks for the undeclared `is8`.
#[test]
fn a_strict_result_sort_without_a_sort_predicate_is_an_invalid_heat_cool_diagnostic() {
    let source = indoc! {r#"
        module MAIN
          imports BOOL
          syntax 8
          syntax KResult
          syntax Exp ::= foo(Exp) [strict, result(8)] | "e"
        endmodule
    "#};
    let prelude = embedded("prelude.md").unwrap();
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("res8.k", source),
        "MAIN",
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
    let error = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap_err();
    assert_eq!(error.stage, "resolve heat/cool attributes", "{error}");
    // Heating and cooling require the same predicate at the same production location.
    assert_eq!(error.diagnostics.len(), 1, "{error}");
    for diagnostic in &error.diagnostics {
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidHeatCool
        );
        assert!(
            diagnostic
                .message
                .starts_with("Definition is missing function is8 required for strictness."),
            "{error}"
        );
    }
}

/// Compiles `source`, whose main module is `MAIN`, with the prelude for the Rust backend.
fn compile_main_with_prelude(
    file: &str,
    source: &str,
) -> Result<k_rust::kompile::CompiledKoreArtifacts, k_rust::kompile::CompileError> {
    let prelude = embedded("prelude.md").unwrap();
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new(file, source),
        "MAIN",
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
    compile_loaded_definition(&loaded, CompileOptions::default())
}

#[test]
fn a_strict_result_synonym_compiles_with_denoted_heat_and_cool_predicates() {
    let artifacts = compile_main_with_prelude(
        "result-synonym.k",
        indoc! {r#"
        module MAIN
          imports INT
          syntax R = Int
          syntax Exp ::= f(Int) [strict, result(R), symbol(f)]
        endmodule
    "#},
    )
    .unwrap_or_else(|error| panic!("a strict result synonym should compile: {error}"));
    let conditions = artifacts
        .execution_definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule {
                requires,
                attributes,
                ..
            } if attributes.get("heat").is_some() || attributes.get("cool").is_some() => {
                Some(requires)
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(conditions.len(), 2, "one heating and one cooling condition");
    for condition in conditions {
        let mut predicates = Vec::new();
        condition.visit_preorder(&mut |term| {
            if let Term::Apply { label, .. } = term
                && (label.name == "isInt" || label.name == "isR")
            {
                predicates.push(label.name.clone());
            }
        });
        assert_eq!(predicates, ["isInt"], "{condition}");
    }
}

#[test]
fn an_undeclared_strict_result_reports_one_invalid_heat_cool_diagnostic() {
    let error = compile_main_with_prelude(
        "undeclared-result.k",
        indoc! {r#"
        module MAIN
          imports INT
          syntax Exp ::= f(Int) [strict, result(Foo), symbol(f)]
        endmodule
    "#},
    )
    .unwrap_err();
    assert_eq!(error.stage, "resolve heat/cool attributes", "{error}");
    assert_eq!(error.diagnostics.len(), 1, "{error}");
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidHeatCool
    );
    assert!(
        error.diagnostics[0]
            .message
            .starts_with("Definition is missing function isFoo required for strictness."),
        "{error}"
    );
}

/// The compiled definition is the main module's import closure, so a strict production declared
/// in a syntax module finds `isKResult` when the importing main module declares `KResult`: the
/// hybrid rules and the sequential context's side condition both mention it, and the compiled
/// definition declares it.
#[test]
fn a_strict_production_in_a_syntax_module_finds_the_result_predicate_of_the_main_closure() {
    for (file, source) in [
        (
            "hybsplit.k",
            indoc! {r#"
                module MAIN-SYNTAX
                  imports BOOL
                  syntax Val ::= "v"
                  syntax Exp ::= Val | foo(Exp) [strict, hybrid, symbol(foo)]
                endmodule
                module MAIN
                  imports MAIN-SYNTAX
                  syntax KResult ::= Val
                endmodule
            "#},
        ),
        (
            "seqsplit.k",
            indoc! {r#"
                module MAIN-SYNTAX
                  imports BOOL
                  syntax Val ::= "v"
                  syntax Exp ::= Val | foo(Exp, Exp) [seqstrict(c), result(Val), symbol(foo)]
                endmodule
                module MAIN
                  imports MAIN-SYNTAX
                  syntax KResult ::= Val
                  context alias [c]: HERE
                endmodule
            "#},
        ),
    ] {
        let artifacts = compile_main_with_prelude(file, source)
            .unwrap_or_else(|error| panic!("{file}: {error}"));
        assert!(
            artifacts
                .definition_kore
                .contains("symbol LblisKResult{}(SortK{}) : SortBool{}"),
            "{file}"
        );
        // Beyond its declaration and its own axioms, the predicate is used by the generated rules.
        assert!(
            artifacts.definition_kore.matches("LblisKResult{}(").count() > 3,
            "{file}"
        );
    }
}

/// A strict production in a module outside the main module's import closure contributes nothing
/// to the compiled definition, so its hybrid rules are not checked for `isKResult`.
#[test]
fn a_hybrid_production_outside_the_main_closure_is_not_checked_for_its_predicate() {
    let source = indoc! {r#"
        module BOOL
        endmodule
        module OTHER
          imports BOOL
          syntax Exp ::= "e" | foo(Exp) [strict, hybrid, symbol(foo)]
        endmodule
        module MAIN
          imports BOOL
        endmodule
    "#};
    resolve_strict(&parsed(source)).unwrap();
}

/// The `NoKTerms` remedy is followable: a definition that declares the predicate of a sort
/// without K terms itself (`is8`, `is#Foo`) compiles, and the compiled definition declares that
/// predicate once, the user's own function, which the heat and cool rules use.
#[test]
fn declaring_the_predicate_of_a_result_sort_without_k_terms_compiles() {
    for (file, sort, sort_declaration, declaration, symbol) in [
        (
            "remedy8.k",
            "8",
            "syntax 8",
            "syntax Bool ::= is8(K) [symbol(is8), function]",
            "Lblis8",
        ),
        (
            "remedyfoo.k",
            "#Foo",
            r#"syntax #Foo ::= "x""#,
            r#"syntax Bool ::= "is#Foo" "(" K ")" [symbol(is#Foo), function]"#,
            "Lblis'Hash'Foo",
        ),
    ] {
        let source = format!(
            "module MAIN\n  imports BOOL\n  {sort_declaration}\n  syntax KResult\n  {declaration}\n  syntax Exp ::= foo(Exp) [strict, result({sort})] | \"e\"\nendmodule\n"
        );
        let artifacts = compile_main_with_prelude(file, &source)
            .unwrap_or_else(|error| panic!("{file}: {error}"));
        assert_eq!(
            artifacts
                .definition_kore
                .matches(&format!("symbol {symbol}{{}}(SortK{{}}) : SortBool{{}}"))
                .count(),
            1,
            "{file}"
        );
        // The heating and the cooling rule each test the strict argument.
        assert!(
            artifacts
                .definition_kore
                .matches(&format!("{symbol}{{}}("))
                .count()
                >= 2,
            "{file}"
        );
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
    let transformed = resolve_semantic_casts(&parsed(source)).unwrap();
    let rule = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let transformed = resolve_semantic_casts(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = constant_fold(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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

/// A loaded parametric label carries no instance. `peq`'s result sort `Bool` does not mention its
/// parameter, so its application folds; `padd`'s result sort is its parameter, which only sort
/// injection instantiates, so its application is left for injection.
#[test]
fn folds_a_parametric_production_only_when_its_result_sort_is_free_of_parameters() {
    let source = indoc! {r#"
        module MAIN
          syntax Int [hook(INT.Int)]
          syntax Bool [hook(BOOL.Bool)]
          syntax Int ::= r"[\\+\\-]?[0-9]+" [token, prec(2)]
          syntax Bool ::= r"true|false" [token]
          syntax Int ::= "f(" Int ")" [function, symbol(f)]
          syntax {S} Bool ::= "peq(" S "," S ")" [function, hook(INT.eq), symbol(peq)]
          syntax {S} S ::= "padd(" S "," S ")" [function, hook(INT.add), symbol(padd)]
          rule f(X) => padd(1, 2)
            requires peq(1, 1)
        endmodule
    "#};
    let transformed = constant_fold(&resolve_semantic_casts(&parsed(source)).unwrap()).unwrap();
    let (right, requires) = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, requires, .. } => match body.unannotated() {
                Term::Rewrite { right, .. } => Some((
                    Printer::new().print_term(right),
                    Printer::new().print_term(requires),
                )),
                _ => None,
            },
            _ => None,
        })
        .unwrap();
    assert_eq!(requires, r#"#token("true","Bool")"#);
    assert!(right.starts_with("padd("), "{right}");
}

/// The right-hand side of the only rule of `source` after constant folding, which never fails.
fn constant_folded_right_hand_side(source: &str) -> Term {
    let transformed = constant_fold(&resolve_semantic_casts(&parsed(source)).unwrap()).unwrap();
    transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => match body.unannotated() {
                Term::Rewrite { right, .. } => Some(right.unannotated().clone()),
                _ => None,
            },
            _ => None,
        })
        .unwrap()
}

/// `I >>Int N` is the floor of I / 2^N for every natural N, so `0 >>Int N` folds to 0 however
/// large N is. A shift by a negative amount is undefined (`domains.md`); no token denotes it, so
/// it stays as written for execution, and the definition still compiles.
#[test]
fn folds_right_shifts_by_any_natural_amount() {
    let control =
        include_str!("fixtures/reference/kompile/constant-folding-integer-bounds/control.k");
    assert_eq!(
        constant_folded_right_hand_side(&control.replace("0 >>Int 2147483647", "8 >>Int 1")),
        Term::Token {
            token: "4".into(),
            sort: Sort::new("Int"),
        }
    );
    let shifted = include_str!("fixtures/reference/kompile/constant-folding-integer-bounds/test.k");
    for value in [
        "2147483647",
        "2147483648",
        "4294967295",
        "4294967296",
        "18446744073709551616",
    ] {
        assert_eq!(
            constant_folded_right_hand_side(&shifted.replace("2147483648", value)),
            Term::Token {
                token: "0".into(),
                sort: Sort::new("Int"),
            },
            "0 >>Int {value}"
        );
    }
    assert_eq!(
        Printer::new().print_term(&constant_folded_right_hand_side(
            &shifted.replace("2147483648", "-1")
        )),
        r#"shrInt(#token("0","Int"),#token("-1","Int"))"#
    );
}

/// A folded value is part of the emitted definition, so the fold writes none above 2^20 bits, its
/// own bound (never above the backend's on `^Int` results); a larger one stays for execution.
#[test]
fn leaves_results_above_the_result_bound_unfolded() {
    let source = |exponent: &str| {
        format!(
            r#"
            module MAIN
              syntax Int [hook(INT.Int)]
              syntax Int ::= r"[\\+\\-]?[0-9]+" [token]
              syntax Int ::= "result" [function, symbol(result)]
              syntax Int ::= Int "^Int" Int [function, hook(INT.pow), symbol(powInt)]
              rule result => 2 ^Int {exponent}
            endmodule
            "#
        )
    };
    let folded = constant_folded_right_hand_side(&source("1048575"));
    let Term::Token { token, .. } = &folded else {
        panic!("2 ^Int 1048575 has 2^20 bits and folds");
    };
    assert_eq!(token.len(), 315_653);
    assert_eq!(
        Printer::new().print_term(&constant_folded_right_hand_side(&source("1048576"))),
        r#"powInt(#token("2","Int"),#token("1048576","Int"))"#
    );
}

/// `String2Id` (`STRING.string2token`) of a literal folds to the token of the result sort whose
/// text is the string, and `Id2String` (`STRING.token2string`) of a token to its text.
#[test]
fn folds_string_and_token_conversions() {
    let source = |right: &str| {
        format!(
            r#"
            module MAIN
              syntax String [hook(STRING.String)]
              syntax Id [token]
              syntax Id ::= "idResult" [function, symbol(idResult)]
              syntax String ::= "stringResult" [function, symbol(stringResult)]
              syntax Id ::= String2Id(String) [function, total, hook(STRING.string2token), symbol(String2Id)]
              syntax String ::= Id2String(Id) [function, total, hook(STRING.token2string), symbol(Id2String)]
              {right}
            endmodule
            "#
        )
    };
    assert_eq!(
        constant_folded_right_hand_side(&source(
            r#"rule idResult => String2Id(#token("\"_42\"", "String"))"#
        )),
        Term::Token {
            token: "_42".into(),
            sort: Sort::new("Id"),
        }
    );
    assert_eq!(
        constant_folded_right_hand_side(&source(
            r#"rule stringResult => Id2String(#token("x", "Id"))"#
        )),
        Term::Token {
            token: r#""x""#.into(),
            sort: Sort::new("String"),
        }
    );
}

/// Hooks the fold has no implementation for, such as the deprecated `STRING.category` and
/// `STRING.directionality` whose meaning `domains.md` does not give, stay as written.
#[test]
fn leaves_hooks_without_a_fold_implementation_unfolded() {
    let source = indoc! {r#"
        module MAIN
          syntax String [hook(STRING.String)]
          syntax String ::= "result" [function, symbol(result)]
          syntax String ::= categoryChar(String) [function, hook(STRING.category), symbol(categoryChar)]
                          | directionalityChar(String) [function, hook(STRING.directionality), symbol(directionalityChar)]
          rule result => categoryChar(directionalityChar(#token("\"a\"", "String")))
        endmodule
    "#};
    assert_eq!(
        Printer::new().print_term(&constant_folded_right_hand_side(source)),
        r#"categoryChar(directionalityChar(#token("\"a\"","String")))"#
    );
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = constant_fold(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
fn folds_string_concat_into_a_token_escaping_non_ascii_code_points() {
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
    let Sentence::Rule { body, .. } = &*transformed.main_module().unwrap().local_sentences[2]
    else {
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
    let source = |value: &str| {
        format!(
            r#"
            module MAIN
              syntax Int [hook(INT.Int)]
              syntax String [hook(STRING.String)]
              syntax Int ::= r"[\\+\\-]?[0-9]+" [token]
              syntax String ::= r"[\\\"][^\\\"]*[\\\"]" [token]
              syntax String ::= "result" [function, symbol(result)]
              syntax String ::= "chr(" Int ")" [function, hook(STRING.chr), symbol(chr)]
              rule result => chr({value})
            endmodule
            "#
        )
    };
    let folded = |value: &str| {
        let transformed =
            constant_fold(&resolve_semantic_casts(&parsed(&source(value))).unwrap()).unwrap();
        let right = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
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

    // A number outside the code points is no character (undefined), and whether a String holds a
    // surrogate code point the definition does not settle (unspecified): the fold computes
    // neither, and `chrChar` of one stays as written.
    for codepoint in ["-1", "1114112", "55296", "57343"] {
        let right = constant_folded_right_hand_side(&source(codepoint));
        assert_eq!(
            Printer::new().print_term(&right),
            format!("chr(#token(\"{codepoint}\",\"Int\"))"),
            "code point {codepoint}"
        );
    }
}

/// `1 /Int 0` is undefined (`domains.md`: division by zero is `#False`); no token denotes it, so
/// the fold leaves it and the definition compiles.
#[test]
fn leaves_an_undefined_constant_operation_unfolded() {
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
    let transformed = constant_fold(&definition).unwrap();
    let Sentence::Rule { body, .. } = &*transformed.main_module().unwrap().local_sentences[2]
    else {
        unreachable!()
    };
    let Term::Rewrite { right, .. } = body.unannotated() else {
        unreachable!()
    };
    assert_eq!(
        Printer::new().print_term(right),
        r#"divide(#token("1","Int"),#token("0","Int"))"#
    );
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
        .filter_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
fn guard_or_patterns_preserves_resolved_production_for_top_cell_alias_sort() {
    let binary_production = |sort: &str| Sentence::Production {
        label: Some(Label::new("#Or")),
        parameters: Vec::new(),
        sort: Sort::new(sort),
        items: vec![
            ProductionItem::NonTerminal {
                sort: Sort::new(sort),
                name: None,
            },
            ProductionItem::NonTerminal {
                sort: Sort::new(sort),
                name: None,
            },
        ],
        attributes: Attributes::default(),
    };
    let mut definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("top-a", "TopCell", Attributes::default()),
                production("top-b", "TopCell", Attributes::default()),
                binary_production("TopCell"),
                binary_production("K"),
                rule(
                    application(
                        "#Or",
                        vec![
                            application("top-a", Vec::new()),
                            application("top-b", Vec::new()),
                        ],
                    ),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let top_cell_or_identity = {
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        let production = catalog
            .productions_for(&LabelHead::from(&Label::new("#Or")))
            .iter()
            .copied()
            .find(|production| {
                matches!(
                    catalog.production(*production),
                    Sentence::Production { sort, .. } if sort == &Sort::new("TopCell")
                )
            })
            .unwrap();
        catalog.identity(production)
    };
    let metadata = TermMetadata {
        span: Some(TermSpan {
            source: SourceId(0),
            start: 10,
            end: 30,
        }),
        production: Some(top_cell_or_identity),
        ..TermMetadata::default()
    };
    let sentence = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .last_mut()
        .unwrap();
    let Sentence::Rule { body, .. } = k_rust::definition::sentence_mut(sentence) else {
        unreachable!()
    };
    let taken = std::mem::replace(body, Term::Sequence(Vec::new()));
    *body = taken.with_metadata(metadata.clone());

    let transformed = guard_or_patterns(&definition).unwrap();
    let Sentence::Rule { body, .. } = &**transformed
        .main_module()
        .unwrap()
        .local_sentences
        .last()
        .unwrap()
    else {
        unreachable!()
    };
    let Term::As { pattern, alias } = body.unannotated() else {
        panic!("#Or should be guarded by an alias: {body:?}");
    };

    assert!(matches!(
        pattern.unannotated(),
        Term::Apply { label, .. } if label.name == "#Or"
    ));
    let pattern_metadata = pattern
        .metadata()
        .expect("guarded #Or should retain semantic metadata");
    assert_eq!(pattern_metadata.span, metadata.span);
    assert_eq!(pattern_metadata.production, metadata.production);
    assert!(matches!(
        alias.unannotated(),
        Term::Variable {
            name,
            sort: Some(sort),
        } if name == "_Gen0" && sort == &Sort::new("TopCell")
    ));
}

#[test]
fn guard_or_patterns_propagates_sort_inference_errors() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                Sentence::Production {
                    label: Some(Label::new("#Or")),
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
                    attributes: Attributes::default(),
                },
                production("a", "Exp", Attributes::default()),
                rule(
                    application("#Or", vec![application("a", Vec::new())]),
                    attributes(&[
                        ("org.kframework.attributes.Source", json!("or.k")),
                        ("org.kframework.attributes.Location", json!([7, 3, 7, 20])),
                    ]),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };

    let error = guard_or_patterns(&definition).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidOrPattern
    );
    assert_eq!(
        error.diagnostics[0].message,
        "KLabel \"#Or\" expects 2 arguments but received 1"
    );
    assert_eq!(error.diagnostics[0].source.as_deref(), Some("or.k"));
    assert_eq!(error.diagnostics[0].location.unwrap().start_line, 7);
}

#[cfg(feature = "z3-inference")]
#[test]
fn complete_top_cell_or_compiles_with_a_top_cell_guard_alias() {
    let source = include_str!("fixtures/reference/guard-or/complete-top-branches.k");
    let artifacts = compile_fixture("complete-top-branches.k", source, "COMPLETE-TOP-BRANCHES");
    let emitted =
        parse_definition(&artifacts.definition_kore).expect("emitted definition should parse");
    let reference = parse_pattern(include_str!(
        "fixtures/reference/guard-or/reference-complete-top-branches-rule.kore"
    ))
    .expect("pinned K authored rule should parse");
    assert!(
        emitted.modules.iter().any(|module| {
            module.name == "COMPLETE-TOP-BRANCHES"
                && module.sentences.iter().any(|sentence| {
                    matches!(
                        sentence,
                        KoreSentence::Axiom { pattern, .. } if pattern.as_ref() == &reference
                    )
                })
        }),
        "emitted definition should contain the pinned semantic authored rule"
    );
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
    let definition = resolve_semantic_casts(&definition).unwrap();
    let (transformed, next_fresh) = resolve_fresh_config_constants(&definition).unwrap();
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
fn a_named_field_projection_is_not_total_with_a_sort_polymorphic_generator() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bar ::= mk(x: Int) [symbol(mk)]
          syntax {S} S ::= wrap(S) [symbol(wrap)]
        endmodule
    "#};
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let transformed = generate_sort_projections(&definition).unwrap();
    let projections = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name == "project:mk:x" => Some((
                label.name.as_str(),
                attributes.get("function").is_some(),
                attributes.get("total").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    // `wrap{Bar}(mk(1))` is also a value of Bar, and the field rule only projects from `mk`.
    assert_eq!(projections, vec![("project:mk:x", true, false)]);
    assert_has_generated_by(&transformed, GeneratingPass::GenerateSortProjections);
}

#[test]
fn a_cell_map_key_projection_is_not_total_with_a_sort_polymorphic_generator() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= wrap(S) [symbol(wrap)]
          configuration <items> <item multiplicity="*" type="Map"> <id> 0 </id> </item> </items>
          syntax K
          syntax Map
        endmodule
    "#};
    assert_eq!(cell_map_key_projection_attributes(source), (true, false));
}

#[test]
fn a_cell_map_key_projection_is_total_without_a_sort_polymorphic_generator() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <items> <item multiplicity="*" type="Map"> <id> 0 </id> </item> </items>
          syntax K
          syntax Map
        endmodule
    "#};
    assert_eq!(cell_map_key_projection_attributes(source), (true, true));
}

fn cell_map_key_projection_attributes(source: &str) -> (bool, bool) {
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let transformed = generate_sort_projections(&definition).unwrap();
    let twice = generate_sort_projections(&transformed).unwrap();
    assert_eq!(
        transformed, twice,
        "cell-map key totality must be idempotent"
    );
    transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| {
            let Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } = &**sentence
            else {
                return None;
            };
            (label.name == "ItemCellMapKey").then(|| {
                (
                    attributes.get("function").is_some(),
                    attributes.get("total").is_some(),
                )
            })
        })
        .expect("configuration expansion must generate the cell-map key projection")
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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

/// An `owise` macro rule applies only where no other rule of its head applies, so it yields to
/// a rule of any explicit priority, including one numbered above the default.
#[test]
fn an_owise_macro_rule_yields_to_every_explicit_priority() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "c" [symbol(c)]
                       | "m(" Exp ")" [macro, symbol(m)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
          rule m(a) => b [priority(250)]
          rule m(_) => c [owise]
          rule pair(m(a), m(b)) => pair(a, b) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("subject") => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(
        output,
        "pair(b(.KList),c(.KList))=>pair(a(.KList),b(.KList))"
    );
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
        let definition = resolve_semantic_casts(&parsed(&source)).unwrap();
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
                ParsedProgram::from_term(application("m", vec![application("a", Vec::new())])),
                &Sort::new("KItem"),
            )
            .unwrap()
            .into_term(),
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
        let definition = resolve_semantic_casts(&parsed(&source)).unwrap();

        assert_eq!(
            expand_macros_in_term(
                &definition,
                "MAIN",
                ParsedProgram::from_term(application("m", vec![application("a", Vec::new())])),
                &Sort::new("KItem"),
            )
            .unwrap()
            .into_term(),
            application("f", vec![application("a", Vec::new())]),
            "production attribute {macro_kind}",
        );
    }
}

/// A parsed program is expanded at its read sort: `m(1)` has the `Int` instance fixed by its
/// argument and takes the rule about `m{Int}`, while `m(a)` has the `Exp` instance and survives.
#[test]
fn parametric_macro_expands_in_a_parsed_program_by_its_argument_sort() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= "a" [symbol(a)]
          syntax {S} S ::= "m(" S ")" [macro, symbol(m)]
          rule m(X:Int) => X
        endmodule
    "#};
    let definition = parsed(source);
    let prepared = MacroExpansionDefinition::prepare(&definition).unwrap();
    let program = |sort: &str, text: &str| {
        k_rust::inner::parse_program(
            &definition,
            "MAIN",
            &Sort::new(sort),
            text,
            k_rust::provenance::SourceId(0),
        )
        .unwrap()
    };

    let int = program("Int", "m(1)");
    let Term::Apply { label, .. } = int.typed_term().unannotated() else {
        panic!("{int:?}")
    };
    assert_eq!(label.parameters, [Sort::new("Int")], "{int:?}");
    assert_eq!(
        prepared
            .expand_program("MAIN", int, &Sort::new("Int"))
            .unwrap()
            .into_term(),
        Term::Token {
            token: "1".into(),
            sort: Sort::new("Int"),
        }
    );

    let exp = program("Exp", "m(a)");
    let expanded = prepared
        .expand_program("MAIN", exp.clone(), &Sort::new("Exp"))
        .unwrap();
    assert_eq!(
        expanded.term(),
        &application("m", vec![application("a", Vec::new())]),
        "an Exp argument does not match X:Int"
    );
}

/// One parametric production with two macro rules that only their result sorts separate: each
/// rule is an axiom about one instance of `m`, so a program application expands by the rule of
/// its own instance, whichever comes first, and an instance neither rule states stays as it is.
#[test]
fn parametric_macro_rules_apply_only_at_their_head_instance() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "true" [token] | "false" [token]
          syntax Exp ::= "a" [symbol(a)]
          syntax {S} S ::= "m" "(" ")" [macro, symbol(m)]
          rule m():Int => 1
          rule m():Bool => true
        endmodule
    "#};
    let definition = parsed(source);
    let prepared = MacroExpansionDefinition::prepare(&definition).unwrap();
    let program = |sort: &str| {
        k_rust::inner::parse_program(
            &definition,
            "MAIN",
            &Sort::new(sort),
            "m()",
            k_rust::provenance::SourceId(0),
        )
        .unwrap()
    };
    for (sort, token) in [("Bool", "true"), ("Int", "1")] {
        let term = program(sort);
        let Term::Apply { label, .. } = term.typed_term().unannotated() else {
            panic!("{term:?}")
        };
        assert_eq!(label.parameters, [Sort::new(sort)], "{term:?}");
        assert_eq!(
            prepared
                .expand_program("MAIN", term, &Sort::new(sort))
                .unwrap()
                .into_term(),
            Term::Token {
                token: token.into(),
                sort: Sort::new(sort),
            },
            "m{{{sort}}}()"
        );
    }
    let exp = program("Exp");
    assert_eq!(
        prepared
            .expand_program("MAIN", exp.clone(), &Sort::new("Exp"))
            .unwrap()
            .term(),
        &application("m", Vec::new())
    );
}

/// The instance of a macro rule's head is the one the typing of the rule gives it. When nothing
/// fixes it (`m() => n()`, both parametric in their result only) it stays open and the rule
/// applies to `m{Bool}()`; an unsorted variable on the right (`m() => X`) is typed at `K`, so that
/// rule is about `m{K}` and leaves `m{Bool}()` alone.
#[test]
fn a_parametric_macro_head_takes_the_instance_its_rule_is_typed_at() {
    let expand = |rule: &str, sort: &str| {
        let source = format!(
            "module MAIN\n  syntax Bool ::= \"true\" [token] | \"false\" [token]\n  \
             syntax {{S}} S ::= \"m\" \"(\" \")\" [macro, symbol(m)]\n  \
             syntax {{S}} S ::= \"n\" \"(\" \")\" [symbol(n)]\n  rule {rule}\nendmodule\n"
        );
        let definition = parsed(&source);
        let program = k_rust::inner::parse_program(
            &definition,
            "MAIN",
            &Sort::new(sort),
            "m()",
            k_rust::provenance::SourceId(0),
        )
        .unwrap();
        let expanded = MacroExpansionDefinition::prepare(&definition)
            .unwrap()
            .expand_program("MAIN", program, &Sort::new(sort))
            .unwrap();
        Printer::new().print_term(expanded.term())
    };
    assert_eq!(expand("m() => n()", "Bool"), "n(.KList)");
    assert_eq!(expand("m() => X", "Bool"), "m(.KList)");
    assert!(expand("m() => X", "K").starts_with("_Gen"));
}

/// An item of a right-hand K sequence is typed in the sequence's `K` context, where it keeps the
/// sort `K`: `m() ~> .K` applies the macro rule about `m{K}` (`m() => X`, whose unsorted `X` is
/// typed at `K`), not the `m{KItem}` one listed first.
#[test]
fn a_parametric_macro_in_a_k_sequence_takes_the_k_instance() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "b" [symbol(b)] | "c" [symbol(c)]
          syntax {S} S ::= "m" "(" ")" [macro, symbol(m)]
          syntax K ::= "f" "(" ")" [function, symbol(f)]
          rule m():KItem => b
          rule m() => X
          rule f() => m() ~> .K
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let expanded = expand_macros(&definition).unwrap();
    let bodies = expanded
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(Printer::new().print_term(body)),
            _ => None,
        })
        .filter(|body| body.starts_with("f("))
        .collect::<Vec<_>>();
    assert_eq!(bodies.len(), 1, "{bodies:?}");
    assert!(bodies[0].contains("_Gen"), "{bodies:?}");
    assert!(!bodies[0].contains("b("), "{bodies:?}");
}

/// The instance of an application is read after its arguments are expanded: `m()` becomes the
/// `Bool` `true`, so the enclosing `f` stands at `Bool`, and the macro rule of `f`'s `KItem`
/// instance does not apply to it.
#[test]
fn a_parametric_macro_sees_the_instance_of_its_expanded_arguments() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token] | "false" [token]
          syntax KItem ::= Bool
          syntax {S} S ::= "m" "(" ")" [macro, symbol(m)]
          syntax {S} S ::= "f" "(" S ")" [macro, symbol(f)]
          rule m() => true
          rule f(X:KItem) => X
        endmodule
    "#};
    let definition = parsed(source);
    let term = application("f", vec![application("m", Vec::new())]);
    let expanded = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(term),
        &Sort::new("Bool"),
    )
    .unwrap();
    assert_eq!(
        Printer::new().print_term(expanded.term()),
        r#"f(#token("true","Bool"))"#
    );
}

/// A downcast places `f(A)` at `Bool`, but the label's own instance is fixed by its `KItem`
/// argument (injection projects the `KItem` result to `Bool`); the structured macro rule
/// `f(X):Bool => true`, about `f{Bool}` and with an unsorted `X` that matches any argument,
/// does not apply to it.
#[test]
fn a_parametric_macro_reads_the_label_instance_under_a_downcast() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token] | "false" [token]
          syntax KItem ::= Bool
          syntax {S} S ::= "f" "(" S ")" [macro, symbol(f)]
        endmodule
    "#};
    let mut definition = parsed(source);
    let at_bool = |term: Term| {
        term.with_metadata(TermMetadata {
            sort: Some(Sort::new("Bool")),
            ..TermMetadata::default()
        })
    };
    let truth = || Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    let mut attributes = Attributes::default();
    attributes.mark(k_rust::definition::AttributeKey::Macro);
    definition.modules[0]
        .local_sentences
        .push(std::sync::Arc::new(Sentence::Rule {
            body: rewrite(
                at_bool(application("f", vec![Term::variable("X")])),
                truth(),
            ),
            requires: truth(),
            ensures: truth(),
            attributes,
        }));
    // The shape semantic-cast resolution gives `{f(A)}:>Bool`: the cast is the sort metadata.
    let term = at_bool(application(
        "f",
        vec![Term::Variable {
            name: "A".into(),
            sort: Some(Sort::new("KItem")),
        }],
    ));
    let expanded = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(term.clone()),
        &Sort::new("Bool"),
    )
    .unwrap();
    assert_eq!(expanded.term(), &term);
    // The same rule applies where the label's instance is `Bool`.
    let at_instance = application(
        "f",
        vec![Term::Variable {
            name: "B".into(),
            sort: Some(Sort::new("Bool")),
        }],
    );
    assert_eq!(
        expand_macros_in_term(
            &definition,
            "MAIN",
            ParsedProgram::from_term(at_instance),
            &Sort::new("KItem")
        )
        .unwrap()
        .into_term(),
        truth()
    );
}

/// `g(x)` does not type until the token macro `x => 1` rewrites it, so the instance of `m()` is
/// unknown when it is first tried: the macro rule about `m{Int}`, listed first, must not take
/// it. Once the sentence types, `m()` is retried at its `Bool` instance.
#[test]
fn a_parametric_macro_waits_for_the_sentence_to_type() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Bool ::= "true" [token] | "false" [token]
          syntax Pair ::= "pair" "(" Bool "," Int ")" [symbol(pair)]
          syntax Int ::= "g" "(" Int ")" [symbol(g)]
          syntax Foo ::= Int
          syntax Foo ::= "x" [token]
          syntax {S} S ::= "m" "(" ")" [macro, symbol(m)]
          rule m():Int => 0
          rule m():Bool => false
          rule x => 1 [macro]
        endmodule
    "#};
    let definition = parsed(source);
    let term = application(
        "pair",
        vec![
            application("m", Vec::new()),
            application(
                "g",
                vec![Term::Token {
                    token: "x".into(),
                    sort: Sort::new("Foo"),
                }],
            ),
        ],
    );
    let expanded = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(term),
        &Sort::new("KItem"),
    )
    .unwrap();
    assert_eq!(
        Printer::new().print_term(expanded.term()),
        r#"pair(#token("false","Bool"),g(#token("1","Int")))"#
    );
}

fn sibling_macro_definition() -> Definition {
    let source = indoc! {r#"
        module MAIN
          syntax K
          syntax Map
          syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | go() [symbol(go)]
          syntax Top ::= Foo | c() [macro, symbol(c)]
          syntax {S} P ::= pair2(S, S) [symbol(pair2)]
          syntax {S} S ::= m() [macro, symbol(m)]
          rule c() => a
          rule m():Foo => b
          rule <k> go() => pair2(m(), c()) ... </k>
          configuration <k> $PGM:KItem </k>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    propagate_macro_attributes(&definition).unwrap()
}

/// The two arguments share `pair2`'s parameter: `m` is initially at `Top`, but rewriting its
/// sibling `c` to `a` puts it at `Foo`, where its macro rule applies.
#[test]
fn a_parametric_macro_is_retried_after_a_sibling_rewrite() {
    let definition = sibling_macro_definition();
    let expanded = expand_macros(&definition).unwrap();
    let mut right_sides = Vec::new();
    for sentence in &expanded.main_module().unwrap().local_sentences {
        if let Sentence::Rule { body, .. } = &**sentence {
            body.visit_preorder(&mut |term| {
                if let Term::Rewrite { left, right } = term.unannotated()
                    && let Term::Apply { label, .. } = left.unannotated()
                    && label.name == "go"
                {
                    right_sides.push(Printer::new().print_term(right));
                }
            });
        }
    }
    assert_eq!(right_sides, ["pair2(b(.KList),a(.KList))"]);
}

/// Positioned ground expansion retries `m{Top}` at `Foo` after its sibling rewrites.
#[test]
fn a_ground_parametric_macro_is_retried_after_a_sibling_rewrite() {
    let definition = sibling_macro_definition();
    let term = application(
        "pair2",
        vec![application("m", Vec::new()), application("c", Vec::new())],
    );
    let expanded = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(term),
        &Sort::new("KItem"),
    )
    .unwrap();
    assert_eq!(
        Printer::new().print_term(expanded.term()),
        "pair2(b(.KList),a(.KList))"
    );
}

/// The inner `w` introduces its own applied-rule set. After its `m` retry rewrites,
/// the outer `w` must use its own set so that the same non-recursive rule can apply there.
#[test]
fn a_macro_ancestor_is_retried_with_its_own_applied_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax K
          syntax Map
          syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | go() [symbol(go)]
          syntax Top ::= Foo | c() [macro, symbol(c)]
          syntax {S} P ::= pair2(S, S) [symbol(pair2)]
          syntax {S} S ::= m() [macro, symbol(m)]
          syntax P ::= w(P) [macro, symbol(w)]
          rule c() => a
          rule m():Foo => b
          rule w(pair2(b, a)) => pair2(m(), c())
          rule <k> go() => w(w(pair2(b, a))) ... </k>
          configuration <k> $PGM:KItem </k>
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let expanded = expand_macros(&definition).unwrap();
    let mut right_sides = Vec::new();
    for sentence in &expanded.main_module().unwrap().local_sentences {
        if let Sentence::Rule { body, .. } = &**sentence {
            body.visit_preorder(&mut |term| {
                if let Term::Rewrite { left, right } = term.unannotated()
                    && let Term::Apply { label, .. } = left.unannotated()
                    && label.name == "go"
                {
                    right_sides.push(Printer::new().print_term(right));
                }
            });
        }
    }
    assert_eq!(right_sides, ["pair2(b(.KList),a(.KList))"]);
}

/// A structured macro rule `a => a:Int` only adds a downcast to `a`, so the expanded term is
/// equal to the parsed one, but `f`'s instance then follows the `Int` argument: the parsed
/// `f{KItem}` no longer holds, and the macro rule about `f{Int}` applies instead of the `KItem`
/// one.
#[test]
fn a_parametric_macro_sees_a_rewrite_that_changes_only_metadata() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Foo ::= Int
          syntax Foo ::= "a" [symbol(a)]
          syntax KItem ::= Foo
          syntax Exp ::= "b" [symbol(b)] | "c" [symbol(c)]
          syntax {S} S ::= "f" "(" S ")" [macro, symbol(f)]
          rule f(_):KItem => b
          rule f(_):Int => 0
        endmodule
    "#};
    let mut definition = parsed(source);
    let mut attributes = Attributes::default();
    attributes.mark(k_rust::definition::AttributeKey::Macro);
    definition.modules[0]
        .local_sentences
        .push(std::sync::Arc::new(Sentence::Rule {
            body: rewrite(
                application("a", Vec::new()),
                application("#SemanticCastToInt", vec![application("a", Vec::new())]),
            ),
            requires: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            ensures: Term::Token {
                token: "true".into(),
                sort: Sort::new("Bool"),
            },
            attributes,
        }));
    let program = k_rust::inner::parse_program(
        &definition,
        "MAIN",
        &Sort::new("KItem"),
        "f(a)",
        k_rust::provenance::SourceId(0),
    )
    .unwrap();
    let Term::Apply { label, .. } = program.typed_term().unannotated() else {
        panic!("{program:?}")
    };
    assert_eq!(label.parameters, [Sort::new("KItem")], "{program:?}");
    let expanded = MacroExpansionDefinition::prepare(&definition)
        .unwrap()
        .expand_program("MAIN", program, &Sort::new("KItem"))
        .unwrap();
    assert_eq!(
        Printer::new().print_term(expanded.term()),
        r#"#token("0","Int")"#
    );
}

/// A parsed program is typed at its position after each rewrite: `m()` becomes the `Bool`
/// `true`, and the `KItem` macro rule of `f` does not apply to the resulting `f(true)`.
/// Parser instances are removed before expansion.
#[test]
fn a_parametric_macro_in_a_parsed_program_is_typed_after_its_arguments_expand() {
    let source = indoc! {r#"
        module MAIN
          syntax Bool ::= "true" [token] | "false" [token]
          syntax KItem ::= Bool
          syntax {S} S ::= "m" "(" ")" [macro, symbol(m)]
          syntax {S} S ::= "f" "(" S ")" [macro, symbol(f)]
          rule m() => true
          rule f(X:KItem) => X
        endmodule
    "#};
    let definition = parsed(source);
    let program = k_rust::inner::parse_program(
        &definition,
        "MAIN",
        &Sort::new("Bool"),
        "f(m())",
        k_rust::provenance::SourceId(0),
    )
    .unwrap();
    let expanded = MacroExpansionDefinition::prepare(&definition)
        .unwrap()
        .expand_program("MAIN", program, &Sort::new("Bool"))
        .unwrap();
    let printed = Printer::new().print_term(expanded.term());
    assert_eq!(printed, r#"f(#token("true","Bool"))"#);
}

/// Whether a rule is a macro rule follows from its attributes and from the production at the
/// root of its left-hand side, so selecting the macro rules does not walk the rest of the other
/// rules: beside an ordinary rule whose left-hand side is 100,000 levels deep, a program is
/// expanded through a macro on a thread of 2 MiB of stack.
#[test]
fn macro_rules_are_selected_without_walking_the_left_sides_of_other_rules() {
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
          syntax KItem ::= "go" [symbol(go)] | done(Nat) [symbol(done)]
                         | "mgo" [macro, symbol(mgo)]
          rule mgo => go
        endmodule
    "#};
    let mut definition = parsed(source);
    let deep = (0..100_000).fold(application("z", Vec::new()), |term, _| {
        application("s", vec![term])
    });
    let truth = || Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .push(std::sync::Arc::new(Sentence::Rule {
            body: rewrite(
                application("done", vec![deep]),
                application("go", Vec::new()),
            ),
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        }));
    let program = k_rust::inner::parse_program(
        &definition,
        "MAIN",
        &Sort::new("KItem"),
        "mgo",
        k_rust::provenance::SourceId(0),
    )
    .unwrap();
    let printed = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let expanded = MacroExpansionDefinition::prepare(&definition)
                .unwrap()
                .expand_program("MAIN", program, &Sort::new("KItem"))
                .unwrap();
            Printer::new().print_term(expanded.term())
        })
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish");
    assert_eq!(printed, "go(.KList)");
}

/// Prepares `source`'s module `MAIN` with `deep_rule` added, and expands the program `mgo`
/// through the macro rule `mgo => go` on a thread of 2 MiB of stack; returns the printed result.
fn expand_mgo_beside(source: &str, deep_rule: Sentence) -> String {
    expand_beside(source, deep_rule, "mgo")
}

/// [`expand_mgo_beside`] for the program `program`.
fn expand_beside(source: &str, deep_rule: Sentence, program: &str) -> String {
    expand_beside_into(source, deep_rule, program, |term| {
        Printer::new().print_term(term)
    })
}

/// [`expand_beside`], with the expanded program read by `read` on the worker's 2 MiB of stack.
fn expand_beside_into<T: Send + 'static>(
    source: &str,
    deep_rule: Sentence,
    program: &str,
    read: fn(&Term) -> T,
) -> T {
    let mut definition = parsed(source);
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .push(std::sync::Arc::new(deep_rule));
    let program = k_rust::inner::parse_program(
        &definition,
        "MAIN",
        &Sort::new("KItem"),
        program,
        k_rust::provenance::SourceId(0),
    )
    .unwrap();
    std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let expanded = MacroExpansionDefinition::prepare(&definition)
                .unwrap()
                .expand_program("MAIN", program, &Sort::new("KItem"))
                .unwrap();
            read(expanded.term())
        })
        .expect("the worker should spawn")
        .join()
        .expect("the worker should finish")
}

/// The expander of a program copies and projects every macro rule of the program's module,
/// recursively, before it expands anything; a macro rule of any depth is prepared on a thread
/// of 2 MiB of stack, here one whose right-hand side is 100,000 levels deep, beside the macro
/// the program uses.
#[test]
fn macro_rules_of_any_depth_are_prepared_on_a_small_stack() {
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
          syntax KItem ::= "go" [symbol(go)] | done(Nat) [symbol(done)]
                         | "mgo" [macro, symbol(mgo)] | "mdeep" [macro, symbol(mdeep)]
          rule mgo => go
        endmodule
    "#};
    let deep = (0..100_000).fold(application("z", Vec::new()), |term, _| {
        application("s", vec![term])
    });
    let deep_rule = rule(
        rewrite(
            application("mdeep", Vec::new()),
            application("done", vec![deep]),
        ),
        Attributes::default(),
    );
    assert_eq!(expand_mgo_beside(source, deep_rule), "go(.KList)");
}

/// Instantiating a macro rule copies its right-hand side into the term being expanded, so the
/// expansion's stack covers the deepest macro rule as well as the input: the program `mdeep`,
/// one level deep, expands on a thread of 2 MiB of stack through `mdeep => done(s(...100,000...
/// (z)))` to that term. The expansion once sized its stack from the input's depth alone and
/// overflowed in the instantiation.
#[test]
fn a_macro_right_side_of_any_depth_is_instantiated_on_a_small_stack() {
    const DEPTH: usize = 100_000;
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
          syntax KItem ::= done(Nat) [symbol(done)] | "mdeep" [macro, symbol(mdeep)]
        endmodule
    "#};
    let deep = (0..DEPTH).fold(application("z", Vec::new()), |term, _| {
        application("s", vec![term])
    });
    let deep_rule = rule(
        rewrite(
            application("mdeep", Vec::new()),
            application("done", vec![deep]),
        ),
        Attributes::default(),
    );
    let (labels, leaf) = expand_beside_into(source, deep_rule, "mdeep", |term| {
        let mut labels = Vec::new();
        let mut term = term;
        while let Term::Apply { label, arguments } = term.unannotated() {
            labels.push(label.name.clone());
            match arguments.as_slice() {
                [argument] => term = argument,
                _ => break,
            }
        }
        (labels, term.to_string())
    });
    assert_eq!(labels.len(), DEPTH + 2);
    assert_eq!(labels[0], "done");
    assert!(labels[1..].iter().take(DEPTH).all(|label| label == "s"));
    assert_eq!(labels[DEPTH + 1], "z");
    assert_eq!(leaf, "z(.KList)");
}

/// A definition with a parametric macro head, `mp`, is prepared on a thread of 2 MiB of stack
/// beside a parametric macro rule 2,000 levels deep that the program `mgo` never applies: the
/// rule is copied and projected, and the typing views of both modules are built. The rule's
/// head is not typed, since no subject with that head is tried; deeper unused parametric rules
/// are checked under a memory limit by
/// `a_parametric_macro_rule_a_program_never_applies_is_not_typed`.
#[test]
fn parametric_macro_rules_a_program_does_not_apply_are_prepared_on_a_small_stack() {
    let (source, deep_rule) = parametric_macro_beside_mgo(2_000);
    assert_eq!(expand_mgo_beside(source, deep_rule), "go(.KList)");
}

/// The definition of [`parametric_macro_rules_a_program_does_not_apply_are_prepared_on_a_small_stack`],
/// whose parametric macro rule `mp(X:Nat) => s(...(X))` is `depth` levels deep.
fn parametric_macro_beside_mgo(depth: usize) -> (&'static str, Sentence) {
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
          syntax KItem ::= "go" [symbol(go)] | "mgo" [macro, symbol(mgo)]
          syntax {S} S ::= "mp(" S ")" [macro, symbol(mp)]
          rule mgo => go
        endmodule
    "#};
    let variable = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Nat")),
    };
    let deep = (0..depth).fold(variable.clone(), |term, _| application("s", vec![term]));
    let deep_rule = rule(
        rewrite(application("mp", vec![variable]), deep),
        Attributes::default(),
    );
    (source, deep_rule)
}

/// The environment variable that makes
/// [`deep_parametric_macro_rule_child`] run, in the child process of
/// [`a_parametric_macro_rule_a_program_never_applies_is_not_typed`].
const DEEP_PARAMETRIC_CHILD: &str = "K_RUST_TEST_DEEP_PARAMETRIC_MACRO_CHILD";

/// The work of [`a_parametric_macro_rule_a_program_never_applies_is_not_typed`]; it does nothing
/// unless that test runs it in its child process.
#[test]
fn deep_parametric_macro_rule_child() {
    if std::env::var_os(DEEP_PARAMETRIC_CHILD).is_none() {
        return;
    }
    let (source, deep_rule) = parametric_macro_beside_mgo(100_000);
    assert_eq!(expand_mgo_beside(source, deep_rule), "go(.KList)");
}

/// A program that never applies a parametric macro head pays nothing for typing that head's
/// rules: the expander types a rule of a parametric head (O(N x h) memory in the typing view,
/// which records a path and a subterm at every node) only when a subject with that head is
/// tried. Here the program `mgo` is expanded beside `mp(X:Nat) => s(...100,000...(X))` in a
/// child process limited to 1 GiB of address space; typing that rule would take about 1.6 TB, so
/// a typing made when the expander is built exceeds the limit and the child aborts.
#[cfg(target_os = "linux")]
#[test]
fn a_parametric_macro_rule_a_program_never_applies_is_not_typed() {
    let output = std::process::Command::new("sh")
        .arg("-c")
        .arg(r#"ulimit -v 1048576 && exec "$0" "$@""#)
        .arg(std::env::current_exe().unwrap())
        .args(["--exact", "deep_parametric_macro_rule_child", "--nocapture"])
        .args(["--test-threads", "1"])
        .env(DEEP_PARAMETRIC_CHILD, "1")
        .output()
        .expect("the test binary re-runs itself");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the expansion beside an unused deep parametric macro rule failed under 1 GiB of address space ({}):\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The environment variable that makes [`applied_deep_parametric_macro_rule_child`] run, in the
/// child process of [`a_deep_parametric_macro_rule_a_program_applies_is_typed_in_linear_memory`].
const APPLIED_DEEP_PARAMETRIC_CHILD: &str = "K_RUST_TEST_APPLIED_DEEP_PARAMETRIC_MACRO_CHILD";

/// The work of [`a_deep_parametric_macro_rule_a_program_applies_is_typed_in_linear_memory`]; it
/// does nothing unless that test runs it in its child process.
#[test]
fn applied_deep_parametric_macro_rule_child() {
    if std::env::var_os(APPLIED_DEEP_PARAMETRIC_CHILD).is_none() {
        return;
    }
    let (source, deep_rule) = applied_parametric_macro(APPLIED_DEPTH);
    let (labels, leaf) = expand_beside_into(source, deep_rule, "pair(mp(z), mp(one))", |term| {
        let mut labels = Vec::new();
        let mut term = term;
        while let Term::Apply { label, arguments } = term.unannotated() {
            labels.push(label.name.clone());
            match arguments.first() {
                Some(first) => term = first,
                None => break,
            }
        }
        (labels, term.to_string())
    });
    assert_eq!(labels.len(), APPLIED_DEPTH + 2, "pair, the s and z");
    assert_eq!(labels[0], "pair");
    assert!(labels[1..=APPLIED_DEPTH].iter().all(|label| label == "s"));
    assert_eq!(leaf, "z(.KList)");
}

/// The depth of the `Nat` rule of [`applied_deep_parametric_macro_rule_child`].
const APPLIED_DEPTH: usize = 10_000;

/// Typing a sentence takes memory and time linear in its size: the program `pair(mp(z),
/// mp(one))` applies a parametric macro head whose `Nat` rule is 10,000 levels deep, which the
/// expander types when the first subject with that head is tried, in a child process limited to
/// 1 GiB of address space. The typing view once copied the subterm at every position and keyed
/// every position by its full path, O(N x h): 15.9 GB at 10,000 levels. (The expansion that
/// follows, in the typed mode a parametric head selects, addresses each subterm it visits by its
/// path from the root, O(h) per visit, which keeps this test at 10,000 levels.)
#[cfg(target_os = "linux")]
#[test]
fn a_deep_parametric_macro_rule_a_program_applies_is_typed_in_linear_memory() {
    let output = std::process::Command::new("sh")
        .arg("-c")
        .arg(r#"ulimit -v 1048576 && exec "$0" "$@""#)
        .arg(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "applied_deep_parametric_macro_rule_child",
            "--nocapture",
        ])
        .args(["--test-threads", "1"])
        .env(APPLIED_DEEP_PARAMETRIC_CHILD, "1")
        .output()
        .expect("the test binary re-runs itself");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stdout.contains("1 passed"),
        "the expansion through a deep parametric macro rule failed under 1 GiB of address space ({}):\n{stdout}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The definition of [`a_deep_parametric_macro_rule_is_typed_when_a_program_applies_its_head`],
/// whose `Nat` rule `mp(X:Nat) => s(...(X))` is `depth` levels deep.
fn applied_parametric_macro(depth: usize) -> (&'static str, Sentence) {
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
          syntax Pos ::= "one" [symbol(one)] | p(Pos) [symbol(p)]
          syntax KItem ::= pair(Nat, Pos) [symbol(pair)]
          syntax {S} S ::= "mp(" S ")" [macro, symbol(mp)]
          rule mp(Y:Pos) => p(Y)
        endmodule
    "#};
    let variable = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Nat")),
    };
    let deep = (0..depth).fold(variable.clone(), |term, _| application("s", vec![term]));
    let deep_rule = rule(
        rewrite(application("mp", vec![variable]), deep),
        Attributes::default(),
    );
    (source, deep_rule)
}

/// A program that applies a parametric macro head types the head's rules when the first subject
/// with that head is tried: `mp(z)` takes the `Nat` rule, 2,000 levels deep, and `mp(one)` the
/// `Pos` rule, on a thread of 2 MiB of stack. That the instances typed on first use decide which
/// rule applies is pinned by `parametric_macro_rules_apply_only_at_their_head_instance`.
///
/// It pins that the typing happens, on first use, and gives the instance rule selection needs;
/// that the typing runs on a stack zone measured from the rule's depth, and in memory linear in
/// it, is pinned at 10,000 levels by
/// `a_deep_parametric_macro_rule_a_program_applies_is_typed_in_linear_memory`.
#[test]
fn a_deep_parametric_macro_rule_is_typed_when_a_program_applies_its_head() {
    let source = indoc! {r#"
        module MAIN
          syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
          syntax Pos ::= "one" [symbol(one)] | p(Pos) [symbol(p)]
          syntax KItem ::= pair(Nat, Pos) [symbol(pair)]
          syntax {S} S ::= "mp(" S ")" [macro, symbol(mp)]
          rule mp(Y:Pos) => p(Y)
        endmodule
    "#};
    let variable = Term::Variable {
        name: "X".into(),
        sort: Some(Sort::new("Nat")),
    };
    let deep = (0..2_000).fold(variable.clone(), |term, _| application("s", vec![term]));
    let deep_rule = rule(
        rewrite(application("mp", vec![variable]), deep),
        Attributes::default(),
    );
    let expected = format!(
        "pair({}z(.KList){},p(one(.KList)))",
        "s(".repeat(2_000),
        ")".repeat(2_000)
    );
    let expanded = expand_beside(source, deep_rule, "pair(mp(z), mp(one))");
    assert!(
        expanded == expected,
        "expected s^2000(z) and p(one), got {}...{}",
        &expanded[..expanded.len().min(80)],
        &expanded[expanded.len().saturating_sub(80)..]
    );
}

#[test]
fn one_prepared_macro_definition_expands_each_term_as_a_separate_call() {
    // `g` introduces a right-hand-side variable, so each expansion mints a fresh `_Gen` name;
    // a prepared definition must restart that allocation for every term.
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "f(" Exp ")" [symbol(f)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
                       | "m(" Exp ")" [macro, symbol(m)]
                       | "g(" Exp ")" [macro, symbol(g)]
          rule m(X:Exp) => f(X:Exp)
          rule g(X:Exp) => pair(X:Exp, Y:Exp)
        endmodule
    "#};
    let definition = parsed(source);
    let terms = [
        application("m", vec![application("a", Vec::new())]),
        application(
            "g",
            vec![application("m", vec![application("a", Vec::new())])],
        ),
        application("g", vec![application("a", Vec::new())]),
    ];
    let prepared = MacroExpansionDefinition::prepare(&definition).unwrap();

    for term in terms {
        let program = ParsedProgram::from_term(term);
        assert_eq!(
            prepared
                .expand_program("MAIN", program.clone(), &Sort::new("KItem"))
                .unwrap(),
            expand_macros_in_term(&definition, "MAIN", program, &Sort::new("KItem")).unwrap(),
        );
    }
}

#[test]
fn prepared_macro_definition_matches_whole_definition_preparation() {
    // Casts in macro rules, macro kinds propagated to rules of an importing module, priorities,
    // `owise`, a recursive macro, an alias, and an ordinary rule over a macro-free label.
    let source = indoc! {r#"
        module DATA
          syntax Num ::= "one" [symbol(one)] | "two" [symbol(two)]
          syntax Exp ::= Num
                       | "a" [symbol(a)]
                       | "b" [symbol(b)]
                       | "f(" Exp ")" [symbol(f)]
                       | "pair(" Exp "," Exp ")" [symbol(pair)]
                       | "m(" Exp ")" [macro, symbol(m)]
                       | "r(" Exp ")" [macro-rec, symbol(r)]
                       | "al(" Exp ")" [alias, symbol(al)]
          rule m(X:Num) => f(X:Num)
          rule m(X:Exp) => pair(X:Exp, X:Exp) [priority(60)]
        endmodule
        module MAIN
          imports DATA
          rule r(pair(X:Exp, _Y:Exp)) => r(X:Exp)
          rule r(_X:Exp) => b [owise]
          rule al(X:Exp) => f(m(X:Exp))
          rule f(a) => b
        endmodule
    "#};
    let definition = parsed(source);
    let whole = propagate_macro_attributes(&resolve_semantic_casts(&definition).unwrap()).unwrap();
    let restricted = MacroExpansionDefinition::prepare(&definition).unwrap();
    let reference = MacroExpansionDefinition::prepare(&whole).unwrap();
    let leaf = |label| application(label, Vec::new());
    let terms = [
        application("m", vec![leaf("one")]),
        application("m", vec![leaf("a")]),
        application(
            "r",
            vec![application(
                "pair",
                vec![application("pair", vec![leaf("a"), leaf("b")]), leaf("b")],
            )],
        ),
        application("al", vec![leaf("two")]),
        application("f", vec![leaf("a")]),
        application(
            "pair",
            vec![
                application("m", vec![leaf("two")]),
                application("al", vec![leaf("b")]),
            ],
        ),
    ];

    let mut changed = 0;
    for term in terms {
        let program = ParsedProgram::from_term(term.clone());
        let expanded = restricted
            .expand_program("MAIN", program.clone(), &Sort::new("KItem"))
            .unwrap();
        assert_eq!(
            expanded,
            reference
                .expand_program("MAIN", program, &Sort::new("KItem"))
                .unwrap(),
            "{}",
            Printer::new().print_term(&term),
        );
        changed += usize::from(expanded.term() != &term);
    }
    // Every term but the ordinary `f(a)` applies a macro.
    assert_eq!(changed, 5);
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
        expand_macros_in_term(
            &definition,
            "MAIN",
            ParsedProgram::from_term(term),
            &Sort::new("KItem")
        )
        .unwrap()
        .into_term(),
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
            .find_map(|sentence| match &**sentence {
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
            matches!(catalog.production(catalog.lookup(&production).unwrap()),
            Sentence::Production { label: Some(label), sort, .. }
                if label.name == "box" && sort == &Sort::new("Exp")),
            "{module_name}: expanded macro must retain the Exp overload"
        );
        let argument = &arguments[0];
        let production = argument.metadata().unwrap().production.unwrap();
        assert!(
            matches!(catalog.production(catalog.lookup(&production).unwrap()),
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
        .origins
        .links();

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
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = expand_macros(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(side_condition)).unwrap();
    let mut definition = propagate_macro_attributes(&definition).unwrap();
    let main_module = definition.main_module.clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == main_module)
        .unwrap();
    let attributes = module
        .local_sentences
        .iter_mut()
        .find_map(
            |sentence| match k_rust::definition::sentence_mut(sentence) {
                Sentence::Rule { attributes, .. }
                    if attributes.has(k_rust::definition::AttributeKey::Macro) =>
                {
                    Some(attributes)
                }
                _ => None,
            },
        )
        .expect("macro rule");
    attributes.insert("org.kframework.attributes.Source", json!("macro.k"));
    attributes.insert("org.kframework.attributes.Location", json!([3, 1, 3, 20]));
    let error = expand_macros(&definition).unwrap_err();
    let diagnostic = error
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.message == "Cannot compute macros with side conditions.")
        .expect("side-condition diagnostic");
    assert_eq!(
        diagnostic.code,
        k_rust::diagnostic::DiagnosticCode::InvalidMacroExpansion
    );
    assert_eq!(diagnostic.source.as_deref(), Some("macro.k"));
    assert_eq!(diagnostic.location.unwrap().start_line, 3);

    let invalid_priority = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "m(" Exp ")" [macro, symbol(m)]
          rule m(X:Exp) => X:Exp [priority(not-an-integer)]
          rule m(a) [label(subject)]
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(invalid_priority)).unwrap();
    let mut definition = propagate_macro_attributes(&definition).unwrap();
    let main_module = definition.main_module.clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == main_module)
        .unwrap();
    let attributes = module
        .local_sentences
        .iter_mut()
        .find_map(
            |sentence| match k_rust::definition::sentence_mut(sentence) {
                Sentence::Rule { attributes, .. }
                    if attributes
                        .string(k_rust::definition::AttributeKey::Priority)
                        .is_some() =>
                {
                    Some(attributes)
                }
                _ => None,
            },
        )
        .expect("priority macro rule");
    attributes.insert("org.kframework.attributes.Source", json!("priority.k"));
    attributes.insert("org.kframework.attributes.Location", json!([7, 1, 7, 30]));
    let error = expand_macros(&definition).unwrap_err();
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidMacroExpansion
    );
    assert_eq!(
        error.diagnostics[0].message,
        "Invalid value for priority attribute: not-an-integer. Must be an integer."
    );
    assert_eq!(error.diagnostics[0].source.as_deref(), Some("priority.k"));
    assert_eq!(error.diagnostics[0].location.unwrap().start_line, 7);
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
        .filter_map(|sentence| match &**sentence {
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
        .extend(
            [
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
            ]
            .into_iter()
            .map(std::sync::Arc::new),
        );

    let transformed = add_implicit_computation_cell(&definition).unwrap();
    let claims = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
        } = k_rust::definition::sentence_mut(sentence)
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
            production: Some(catalog.identity(stale)),
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
        .filter_map(|sentence| match &**sentence {
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
                attributes(&[
                    ("org.kframework.attributes.Source", json!("cell.k")),
                    ("org.kframework.attributes.Location", json!([11, 2, 11, 20])),
                ]),
            )],
        )],
        attributes: Attributes::default(),
    };
    let error = add_implicit_computation_cell(&definition).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidMainCell
    );
    assert_eq!(error.diagnostics[0].message, "No main cell found");
    assert_eq!(error.diagnostics[0].source.as_deref(), Some("cell.k"));
    assert_eq!(error.diagnostics[0].location.unwrap().start_line, 11);

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

/// The fresh counter is advanced with `INT`'s `_+Int_`, so a rule drawing a fresh value is given
/// a private `INT` import; a definition without `INT` is told so at the rule.
#[test]
fn fresh_variables_import_int_for_the_counter_or_report_its_absence() {
    let main = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Id ::= r"[a-z]+" [token]
                      | "freshId(" Int ")" [function, freshGenerator, symbol(freshId)]
          syntax Exp ::= Int | Id
          configuration <k> 0 </k>
          rule 0 => !X:Id
          syntax K
          syntax Map
        endmodule
    "#};
    let lowered = |source: &str| {
        let definition = resolve_semantic_casts(&parsed(source)).unwrap();
        let definition = add_implicit_computation_cell(&definition).unwrap();
        resolve_fresh_constants(&definition, 0)
    };
    let transformed = lowered(&format!("module INT\nendmodule\n{main}")).unwrap();
    assert!(
        transformed
            .main_module()
            .unwrap()
            .imports
            .contains(&FlatImport {
                name: "INT".into(),
                public: false,
            })
    );

    let error = lowered(main).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1, "{:?}", error.diagnostics);
    let diagnostic = &error.diagnostics[0];
    assert!(
        diagnostic.message.contains("needs the module INT"),
        "{}",
        diagnostic.message
    );
    assert_eq!(
        diagnostic.location.map(|location| location.start_line),
        Some(7)
    );
}

#[test]
fn resolves_fresh_variables_and_generates_the_counter_configuration() {
    let source = indoc! {r#"
        module INT
        endmodule
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let transformed = resolve_fresh_constants(&definition, 7).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        module INT
        endmodule
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let transformed = resolve_fresh_constants(&definition, 7).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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

fn claim_bodies_after_fresh_constants(definition: &Definition) -> Vec<(String, String)> {
    let definition = resolve_semantic_casts(definition).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let transformed = resolve_fresh_constants(&definition, 0).unwrap();
    transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Claim {
                body, attributes, ..
            } => Some((
                attributes.get_str("label").unwrap_or_default().to_owned(),
                Printer::new().print_term(body),
            )),
            _ => None,
        })
        .collect()
}

#[test]
fn claims_over_declared_cells_leave_the_generated_counter_to_the_path() {
    let source = indoc! {r#"
        module INT
        endmodule
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
                       | "freshInt(" Int ")" [function, freshGenerator, symbol(freshInt)]
          syntax Exp ::= Int | "start" | "st(" Int ")" [symbol(st)]
                       | "pair(" Int "," Int ")" [symbol(pair)]
          configuration <k> 0 </k>
          rule start => st(!N:Int) [label(fresh)]
          claim <k> start => st(X:Int) </k> [label(cells)]
          claim <k> pair(_Gen0:Int, _Gen1:Int) => st(_Gen0:Int) </k> [label(uses-generated-names)]
          claim <k> start => st(C:Int) </k> [label(names-counter)]
          syntax K
          syntax Map
        endmodule
    "#};
    let mut definition = parsed(source);
    // A claim that writes the counter cell itself: the parser of a definition module does not see
    // the counter cell yet, so the cell is attached to the parsed body as a spec module would carry it.
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap();
    for sentence in &mut module.local_sentences {
        if let Sentence::Claim {
            body,
            requires,
            ensures,
            attributes,
        } = &**sentence
            && attributes.get_str("label") == Some("names-counter")
        {
            let counter = Term::Variable {
                name: "C".into(),
                sort: Some(Sort::new("Int")),
            };
            let no_dots = || Term::apply("#noDots", Vec::new());
            let body = Term::apply(
                "#cells",
                vec![
                    body.clone(),
                    Term::apply(
                        "<generatedCounter>",
                        vec![
                            no_dots(),
                            Term::Rewrite {
                                left: Box::new(counter.clone()),
                                right: Box::new(counter),
                            },
                            no_dots(),
                        ],
                    ),
                ],
            );
            *sentence = std::sync::Arc::new(Sentence::Claim {
                body,
                requires: requires.clone(),
                ensures: ensures.clone(),
                attributes: attributes.clone(),
            });
        }
    }
    assert_eq!(
        claim_bodies_after_fresh_constants(&definition),
        vec![
            (
                "cells".to_owned(),
                "#cells(`<k>`(#noDots(.KList),`start_MAIN_Exp`(.KList)=>st(X),#noDots(.KList)),`<generatedCounter>`(#noDots(.KList),_Gen0=>?_Gen1,#noDots(.KList)))".to_owned(),
            ),
            (
                "uses-generated-names".to_owned(),
                "#cells(`<k>`(#noDots(.KList),pair(_Gen0,_Gen1)=>st(_Gen0),#noDots(.KList)),`<generatedCounter>`(#noDots(.KList),_Gen2=>?_Gen3,#noDots(.KList)))".to_owned(),
            ),
            (
                "names-counter".to_owned(),
                "#cells(`<k>`(#noDots(.KList),`start_MAIN_Exp`(.KList)=>st(C),#noDots(.KList)),`<generatedCounter>`(#noDots(.KList),C=>C,#noDots(.KList)))".to_owned(),
            ),
        ]
    );
}

#[test]
fn claims_without_cells_keep_their_body() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Exp ::= Int | "start" | "st(" Int ")" [symbol(st)]
          claim start => st(X:Int) [label(no-cells)]
          syntax K
          syntax Map
        endmodule
    "#};
    assert_eq!(
        claim_bodies_after_fresh_constants(&parsed(source)),
        vec![(
            "no-cells".to_owned(),
            "`start_MAIN_Exp`(.KList)=>st(X)".to_owned()
        )]
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
                &**sentence,
                Sentence::Production { label: Some(label), .. }
                    if label.name == "<generatedCounter>"
            ))
    );
}

#[test]
fn preserves_explicit_cell_variables_while_sorting_cell_fragments() {
    let source = indoc! {r#"
        module INT
        endmodule
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Id ::= "freshId(" Int ")" [function, freshGenerator, symbol(freshId)]
          configuration <k> 0 </k>
          rule 0 => !X:Id
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        let definition = resolve_semantic_casts(&definition).unwrap();
        let definition = add_implicit_computation_cell(&definition).unwrap();
        let definition = resolve_fresh_constants(&definition, 0).unwrap();
        let transformed = concretize_cells(&definition).unwrap();
        let rules = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
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
            .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
        if let Sentence::Rule { body, .. } = k_rust::definition::sentence_mut(sentence)
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
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
                matches!(&***sentence, Sentence::Rule { attributes, .. }
                    if attributes.get("initializer").is_none())
            })
            .expect("fixture has an ordinary rule");
        let Sentence::Rule { body, .. } = k_rust::definition::sentence_mut(rule) else {
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

/// Concretize `rule` (labelled `probe`, with any further `attributes`) under `configuration` and
/// render its body, or return the cell-concretization error messages.
fn concretized_cell_rule(configuration: &str, rule: &str) -> Result<String, Vec<String>> {
    concretized_cell_rule_with(configuration, rule, "")
}

fn concretized_cell_rule_with(
    configuration: &str,
    rule: &str,
    attributes: &str,
) -> Result<String, Vec<String>> {
    concretized_cell_rule_in("", configuration, rule, attributes)
}

/// [`concretized_cell_rule_with`] in a module that also declares `syntax`.
fn concretized_cell_rule_in(
    syntax: &str,
    configuration: &str,
    rule: &str,
    attributes: &str,
) -> Result<String, Vec<String>> {
    let source = format!(
        r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          {syntax}
          configuration {configuration}
          rule {rule} [label(probe){attributes}]
          syntax K
          syntax Map
        endmodule
        "#,
    );
    let definition = resolve_semantic_casts(&parsed(&source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).map_err(|error| {
        error
            .diagnostics
            .into_iter()
            .map(|diagnostic| {
                assert!(
                    diagnostic.location.is_some(),
                    "the error should be located at the rule: {diagnostic:?}"
                );
                diagnostic.message
            })
            .collect::<Vec<_>>()
    })?;
    let bodies = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } if attributes.get_str("label") == Some("probe") => {
                Some(Printer::new().print_term(body))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [body] = bodies.as_slice() else {
        panic!("expected one rule labelled probe, found {bodies:?}")
    };
    Ok(body.clone())
}

const OPTIONAL_IN_THREADS: &str = r#"<top> <k> 0 </k> <ts> <th multiplicity="*" type="Map"> <tid> 0 </tid> <o multiplicity="?"> <ov> 0 </ov> </o> </th> </ts> </top>"#;

/// A conditional term as the K prelude declares it: its sort is a parameter of the production.
const CONDITIONAL: &str = "syntax Bool ::= \"true\"\n syntax {Sort} Sort ::= \"#if\" Bool \"#then\" Sort \"#else\" Sort \"#fi\" [function, symbol(ite)]";

// What completion places among a cell's children, wherever the item stands: terms of a cell sort,
// variables, the empty bag. Every message that rejects an item says so, so the list must include
// what completion does place.
const PLACED: &str = "completion places among a cell's children only terms of a cell sort";

// Completion places each item of a rewrite side among the children of the cell whose body holds
// the rewrite. An item that is neither of a cell sort, a variable nor the empty bag is a term the
// rule writes that no child holds: the rule is rejected with an error naming it as written, never
// compiled without it. `.Bag` writes no child, so on a rewrite side it stands for the unit of the
// slot the other side occupies. A production whose sort is one of its parameters fixes no sort for
// its terms, so the message names none.
#[test]
fn rejects_a_rewrite_side_item_that_no_child_holds_and_names_it() {
    for (syntax, rule, named) in [
        (
            "syntax Bag ::= mko(Int) [function]",
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> => mko(2)) ... </th>",
            "the function `mko(_)` of sort Bag, written on the right side of a rewrite in <th>",
        ),
        (
            "syntax Bag ::= bago(Int)",
            "<th> <tid> 1 </tid> (.Bag => bago(2)) ... </th>",
            "the symbol `bago(_)` of sort Bag, written on the right side of a rewrite in <th>",
        ),
        (
            "",
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> #as O => <o> <ov> 2 </ov> </o>) ... </th>",
            "the alias `O`, written on the left side of a rewrite in <th>",
        ),
        (
            CONDITIONAL,
            "<th> <tid> 1 </tid> (.Bag => #if C:Bool #then <o> <ov> 1 </ov> </o> #else .Bag #fi) ... </th>",
            "the function `#if _ #then _ #else _ #fi`, written on the right side of a rewrite in <th>",
        ),
        (
            "syntax {S} S ::= idb(S) [function]",
            "<th> <tid> 1 </tid> (.Bag => idb(.Bag)) ... </th>",
            "the function `idb(_)`, written on the right side of a rewrite in <th>",
        ),
    ] {
        let errors = concretized_cell_rule_in(syntax, OPTIONAL_IN_THREADS, rule, "")
            .expect_err("the rewrite side holds an item that no child holds");
        assert!(
            errors
                .iter()
                .any(|error| error.contains(named) && error.contains(PLACED)),
            "{rule}: {errors:?}"
        );
    }
    // Completion places an alias of one cell only where it stands in the body itself, and says so.
    let errors = concretized_cell_rule_in(
        "",
        OPTIONAL_IN_THREADS,
        "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> #as O => .Bag) ... </th>",
        "",
    )
    .expect_err("an alias on a rewrite side is not placed");
    assert!(
        errors
            .iter()
            .any(|error| error.contains("(an alias of one cell only outside a rewrite)")),
        "{errors:?}"
    );
}

// A cell-sorted function stands among a cell's children like the cell it denotes, so the list of
// what completion places names terms of a cell sort, not only cells.
#[test]
fn places_a_cell_sorted_function_on_a_rewrite_side_by_its_sort() {
    let body = concretized_cell_rule_in(
        "syntax OCell ::= mkoc(Int) [function]",
        OPTIONAL_IN_THREADS,
        "<th> <tid> 1 </tid> (.Bag => mkoc(2)) ... </th>",
        "",
    )
    .unwrap();
    assert!(body.contains("`.OCell`(.KList)=>"), "{body}");
    assert!(body.contains("mkoc"), "{body}");
}

// An alias `P #as V` of one cell names that cell, so `V` is a term of the cell's sort whatever
// sort parsing gave it from the cell body it is written in (`Bag`), at every occurrence of `V`
// in the rule. The rule compiles, through the whole pipeline, as the one that writes `V` with the
// cell's sort.
#[cfg(feature = "z3-inference")]
#[test]
fn an_alias_of_one_cell_compiles_as_the_alias_written_with_the_cells_sort() {
    let probe = |rule: &str| {
        let source = format!(
            r#"module TEST
  imports INT
  configuration <T> <k> $PGM:Int </k> <a> <y> 0 </y> <z> 0 </z> </a> <b> .K </b> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <env> 0 </env> </thread> </threads> </T>
  rule {rule} [label(probe)]
endmodule
"#
        );
        let kore = compile_fixture("alias.k", &source, "TEST").definition_kore;
        let axiom = kore
            .split("axiom")
            .find(|axiom| axiom.contains(r#"label{}("probe")"#))
            .unwrap_or_else(|| panic!("{rule}: no probe axiom"));
        // The axiom without its attributes, which locate it in the source.
        axiom[..axiom.rfind('[').unwrap()].to_owned()
    };
    for (inferred, written) in [
        (
            "<k> 0 => 1 </k> <a> (<y> Y </y> #as YC) ... </a>",
            "<k> 0 => 1 </k> <a> (<y> Y </y> #as YC:YCell) ... </a>",
        ),
        (
            "<k> 0 => 1 </k> <threads> (<thread> <id> 1 </id> ... </thread> #as TC) ... </threads>",
            "<k> 0 => 1 </k> <threads> (<thread> <id> 1 </id> ... </thread> #as TC:ThreadCell) ... </threads>",
        ),
        // `V` read elsewhere: in another cell, and in the cell `<k>`.
        (
            "<k> 0 => 1 </k> <a> (<y> Y </y> #as YC) ... </a> <b> _ => YC </b>",
            "<k> 0 => 1 </k> <a> (<y> Y </y> #as YC:YCell) ... </a> <b> _ => YC:YCell </b>",
        ),
        (
            "<k> 0 => YC ... </k> <a> (<y> Y </y> #as YC) ... </a>",
            "<k> 0 => YC:YCell ... </k> <a> (<y> Y </y> #as YC:YCell) ... </a>",
        ),
    ] {
        assert_eq!(probe(inferred), probe(written), "{inferred}");
    }
}

// An item written among a cell's children outside any rewrite is placed by the same rule as one
// on a rewrite side, so an item no child holds is rejected with the same message, located in the
// cell's body.
#[test]
fn rejects_a_body_item_that_no_child_holds_and_names_it() {
    for (syntax, rule, named) in [
        (
            "syntax Bag ::= mko(Int) [function]",
            "<th> <tid> 1 </tid> mko(2) ... </th>",
            "the function `mko(_)` of sort Bag, written in <th>",
        ),
        (
            "syntax Bag ::= bago(Int)",
            "<th> <tid> 1 </tid> bago(2) ... </th>",
            "the symbol `bago(_)` of sort Bag, written in <th>",
        ),
        (
            CONDITIONAL,
            "<th> <tid> 1 </tid> #if C:Bool #then <o> <ov> 1 </ov> </o> #else .Bag #fi ... </th>",
            "the function `#if _ #then _ #else _ #fi`, written in <th>",
        ),
    ] {
        let errors = concretized_cell_rule_in(syntax, OPTIONAL_IN_THREADS, rule, "")
            .expect_err("the body holds an item that no child holds");
        assert!(
            errors
                .iter()
                .any(|error| error.contains(named) && error.contains(PLACED)),
            "{rule}: {errors:?}"
        );
    }
}

#[test]
fn the_empty_bag_on_a_rewrite_side_is_the_unit_of_the_other_sides_slot() {
    for (rule, removed) in [
        (
            "<th> <tid> 1 </tid> (<o> <ov> 1 </ov> </o> => .Bag) ... </th>",
            true,
        ),
        (
            "<th> <tid> 1 </tid> (.Bag => <o> <ov> 1 </ov> </o>) ... </th>",
            false,
        ),
    ] {
        let body = concretized_cell_rule(OPTIONAL_IN_THREADS, rule).unwrap();
        let rewrite = if removed {
            r#"`<o>`(`<ov>`(#token("1","Int")))=>`.OCell`(.KList)"#
        } else {
            r#"`.OCell`(.KList)=>`<o>`(`<ov>`(#token("1","Int")))"#
        };
        assert!(body.contains(rewrite), "{rule}: {body}");
    }
}

// A cell written inside a parent that does not contain it in the configuration is never dropped:
// dropping it would compile a rule that matches any content of that cell and never updates it.
// When the cell's configured parent is an ancestor of its written parent, completion lifts it
// into the instance of that ancestor which holds the written parent, so every cell that holds it
// in the compiled rule also holds its written parent. Otherwise the rule is rejected.
#[test]
fn places_a_shallower_misnested_cell_beside_its_written_parent() {
    let body = concretized_cell_rule(
        "<top> <left> <value> 0 </value> </left> <right> 1 </right> </top>",
        "<left> <value> 0 => 2 </value> <right> 1 => 3 </right> ... </left>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<left>`(`<value>`(#token("0","Int")=>#token("2","Int"))),`<right>`(#token("1","Int")=>#token("3","Int"))),_DotVar0)"#
    );
}

#[test]
fn places_a_misplaced_cell_beside_its_written_parent_with_other_cells_unmentioned() {
    let body = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> <c> 0 </c> </a> </top>",
        "<a> <b> X => 1 </b> <k> 5 => 6 </k> ... </a>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<k>`(#token("5","Int")=>#token("6","Int")),`<a>`(`<b>`(X=>#token("1","Int")),_DotVar2)),_DotVar0)"#
    );
}

#[test]
fn places_two_misplaced_cells_beside_their_written_parent() {
    let body = concretized_cell_rule(
        "<top> <k> 0 </k> <s> 0 </s> <a> <b> 0 </b> </a> </top>",
        "<a> <b> X => 1 </b> <k> 5 => 6 </k> <s> 1 => 2 </s> ... </a>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<k>`(#token("5","Int")=>#token("6","Int")),`<s>`(#token("1","Int")=>#token("2","Int")),`<a>`(`<b>`(X=>#token("1","Int")))),_DotVar0)"#
    );
}

#[test]
fn places_a_misplaced_cell_written_inside_a_repeated_cell() {
    let body = concretized_cell_rule(
        r#"<top> <k> 0 </k> <as> <a multiplicity="*" type="Map"> <id> 0 </id> <b> 0 </b> </a> </as> </top>"#,
        "<a> <id> 1 </id> <b> X => 1 </b> <k> 5 => 6 </k> ... </a>",
    )
    .unwrap();
    assert_eq!(body.matches("`<a>`(").count(), 1, "{body}");
    assert_eq!(body.matches("`<k>`(").count(), 1, "{body}");
    assert!(
        body.starts_with(
            r#"`<generatedTop>`(`<top>`(`<k>`(#token("5","Int")=>#token("6","Int")),`<as>`("#
        ),
        "the <k> cell belongs beside <as> under <top>: {body}"
    );
}

#[test]
fn places_a_misplaced_cell_in_the_repeated_ancestor_instance_of_its_written_parent() {
    let body = concretized_cell_rule(
        r#"<top> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <k> 0 </k> <frame> <locals> 0 </locals> </frame> <env> 0 </env> </thread> </threads> </top>"#,
        "<frame> <locals> L => 1 </locals> <env> 5 => 6 </env> </frame>",
    )
    .unwrap();
    // One <thread> holds both the written <frame> and the <env> written inside it.
    assert_eq!(body.matches("`<thread>`(").count(), 1, "{body}");
    assert!(
        body.contains(
            r#"`<frame>`(`<locals>`(L=>#token("1","Int"))),`<env>`(#token("5","Int")=>#token("6","Int"))"#
        ),
        "{body}"
    );
}

#[test]
fn places_a_misplaced_cell_written_alone_inside_a_parent() {
    let body = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<a> <k> 5 => 6 </k> ... </a>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<k>`(#token("5","Int")=>#token("6","Int")),`<a>`(_DotVar2)),_DotVar0)"#
    );
}

// Placing <c> would put it inside <x> and <d>, cells that do not hold <a>: the compiled rule
// would state where <c> is in a part of the configuration the rule does not write.
#[test]
fn rejects_a_misplaced_cell_whose_place_is_in_another_branch() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> <x> <d> <c> 0 </c> </d> </x> </top>",
        "<a> <b> X => 1 </b> <c> 5 => 6 </c> ... </a>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <c> written inside <a> belongs in <d> in the configuration, which does not contain <a>"
        ]
    );
}

// The shape of K's regression case issue-313: <foo> written inside <topCell2> belongs in
// <topCell1>, a sibling subtree; moving it there would contradict the written <topCell2>.
#[test]
fn rejects_a_misplaced_cell_moved_out_of_its_written_parent_into_a_sibling_subtree() {
    let errors = concretized_cell_rule(
        "<k> 0 </k> <topCell1> <foo> 0 </foo> </topCell1> <topCell2> <foos> 1 </foos> </topCell2>",
        "<k> 5 => 10 </k> <topCell2> <foo> 0 </foo> ... </topCell2>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <foo> written inside <topCell2> belongs in <topCell1> in the configuration, which does not contain <topCell2>"
        ]
    );
}

#[test]
fn places_a_misplaced_cell_in_a_missing_ancestor_of_its_written_parent() {
    let body = concretized_cell_rule(
        "<top> <k> 0 </k> <x> <s> 0 </s> <y> <a> <b> 0 </b> </a> </y> </x> </top>",
        "<a> <b> X => 1 </b> <s> 5 => 6 </s> ... </a>",
    )
    .unwrap();
    // <s> lands in the <x> completion builds around <a>, not beside the rule's top.
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<x>`(`<s>`(#token("5","Int")=>#token("6","Int")),`<y>`(`<a>`(`<b>`(X=>#token("1","Int")))))),_DotVar0)"#
    );
}

#[test]
fn places_a_misplaced_cell_written_inside_another_misplaced_cell() {
    let body = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <s> <t> 0 </t> </s> <b> <c> 0 </c> </b> </a> </top>",
        "<b> <c> X => 1 </c> <s> <t> 2 </t> <k> 5 => 6 </k> </s> </b>",
    )
    .unwrap();
    // <s> is lifted out of <b> into <a>, and <k>, lifted out of <s>, rides with it to <top>.
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<k>`(#token("5","Int")=>#token("6","Int")),`<a>`(`<s>`(`<t>`(#token("2","Int"))),`<b>`(`<c>`(X=>#token("1","Int"))))),_DotVar0)"#
    );
}

// A thread has one <frame>: the inner <frame> cannot share the outer one's <thread>, and the
// rule does not write a second <thread>.
#[test]
fn rejects_a_misplaced_cell_written_inside_a_cell_of_its_own_sort_under_a_repeated_ancestor() {
    let errors = concretized_cell_rule(
        r#"<top> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <k> 0 </k> <frame> <locals> 0 </locals> </frame> <env> 0 </env> </thread> </threads> </top>"#,
        "<frame> <locals> L => 1 </locals> <frame> <locals> M </locals> </frame> </frame>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <frame> written inside another <frame>: the configuration never nests a cell in a cell of its own sort"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_written_inside_a_cell_of_its_own_sort() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<a> <b> X => 1 </b> <a> <b> 2 </b> </a> </a>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <a> written inside another <a>: the configuration never nests a cell in a cell of its own sort"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_written_inside_one_of_its_descendants() {
    let errors = concretized_cell_rule(
        r#"<top> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <k> 0 </k> <frame> <locals> 0 </locals> </frame> </thread> </threads> </top>"#,
        "<frame> <locals> L => 1 </locals> <thread> <id> 2 </id> ... </thread> </frame>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        ["Cell <thread> written inside <frame>: the configuration places <frame> inside <thread>"]
    );
}

// <k> lifted out of <frame> belongs in the <thread> that holds that <frame>, which the rule
// gives the explicit <k> 7 </k>.
#[test]
fn rejects_a_misplaced_cell_whose_place_in_its_parents_repeated_instance_is_taken() {
    let errors = concretized_cell_rule(
        r#"<top> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <k> 0 </k> <frame> <locals> 0 </locals> </frame> </thread> </threads> </top>"#,
        "<threads> <frame> <locals> L => 1 </locals> <k> 5 => 6 </k> </frame> <k> 7 </k> </threads>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <frame> belongs in the <thread> that holds <frame>, which already has a <k>"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_whose_place_holds_an_explicit_sibling() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<k> 7 </k> <a> <b> X => 1 </b> <k> 5 => 6 </k> ... </a>",
    )
    .unwrap_err();
    // Both <k> cells belong directly under the one <top>, which holds <a>.
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <a> belongs in the <top> that holds <a>, which already has a <k>"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_that_would_have_to_cross_a_rewrite() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<a> <b> X </b> <k> 5 </k> </a> => <a> <b> 1 </b> <k> 6 </k> </a>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <a> belongs outside <a> in the configuration, and moving it there would take it across a rewrite"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_with_no_enclosing_cell_to_hold_it() {
    let errors = concretized_cell_rule_with(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<a> <b> X => 1 </b> <k> 5 </k> ... </a>",
        ", anywhere",
    )
    .unwrap_err();
    // An `anywhere` rule is not completed to the top cell: its outermost cell is <a>.
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <a> belongs outside <a> in the configuration, and the rule has no enclosing cell to hold it"
        ]
    );
}

// A lifted cell leaves its written parent only through cell bags. Crossing anything else would
// change what the term denotes, so each of these rules is rejected rather than compiled with the
// cell dropped or moved.
#[test]
fn rejects_a_misplaced_cell_that_would_have_to_leave_a_function_argument() {
    let errors = concretized_cell_rule_in(
        "syntax Int ::= f(ACell) [function]",
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "f(<a> <b> X </b> <k> 5 </k> </a>) => X",
        "",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <a> belongs outside <a> in the configuration, and moving it there would cross the symbol f(_)_MAIN_Int_ACell"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_that_would_have_to_leave_a_function_argument_in_a_cell_bag() {
    let errors = concretized_cell_rule_in(
        "syntax Bag ::= g(ACell) [function]",
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<top> g(<a> <b> X </b> <k> 5 </k> </a>) ... </top>",
        "",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <a> belongs outside <a> in the configuration, and moving it there would cross the symbol g(_)_MAIN_Bag_ACell"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_that_would_have_to_leave_an_alias_pattern() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <a> <b> 0 </b> </a> </top>",
        "<top> (<a> <b> X => 1 </b> <k> 5 </k> ... </a> #as A) ... </top>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <k> written inside <a> belongs outside <a> in the configuration, and moving it there would take it out of an alias pattern (#as)"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_that_would_have_to_leave_a_k_sequence() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <s> 0 </s> <a> <b> 0 </b> </a> </top>",
        "<k> <a> <b> X </b> <s> 5 </s> ... </a> ~> K => K </k>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <s> written inside <a> belongs outside <a> in the configuration, and moving it there would take it out of a K sequence"
        ]
    );
}

#[test]
fn rejects_a_misplaced_cell_that_would_have_to_leave_the_contents_of_a_leaf_cell() {
    let errors = concretized_cell_rule(
        "<top> <k> 0 </k> <s> 0 </s> <a> <b> 0 </b> </a> </top>",
        "<k> <a> <b> X </b> <s> 5 </s> ... </a> </k>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <s> written inside <a> belongs outside <a> in the configuration, and moving it there would cross the contents of the leaf cell <k>"
        ]
    );
}

// A complete cell (one argument per declared child, no `#dots`/`#noDots`) states all of its
// children, so a cell lifted out of one of them has no place inside it.
#[test]
fn rejects_a_misplaced_cell_that_would_have_to_leave_a_complete_cell() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> <k> 0 </k> <a> <b> <c> 0 </c> </b> </a> </top>
          rule <a> <b> <c> X => 1 </c> <k> 5 </k> </b> </a> [label(probe)]
          syntax K
          syntax Map
        endmodule
    "#};
    let mut definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let rule = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .iter_mut()
        .find(|sentence| {
            matches!(&***sentence, Sentence::Rule { attributes, .. }
                if attributes.get_str("label") == Some("probe"))
        })
        .expect("fixture has the probe rule");
    let Sentence::Rule { body, .. } = k_rust::definition::sentence_mut(rule) else {
        unreachable!()
    };
    // Make the written <a> complete: its one argument is the written <b>.
    let Term::Apply { label, arguments } = body.unannotated() else {
        panic!("the probe body should be the written <a>: {body:?}")
    };
    assert_eq!(label.name, "<a>");
    let written_b = arguments[1].clone();
    *body = application("<a>", vec![written_b]);
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let error = concretize_cells(&definition).unwrap_err();
    let messages = error
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert_eq!(
        messages,
        [
            "Cell <k> written inside <b> belongs outside <b> in the configuration, and moving it there would cross the complete cell <a>"
        ]
    );
}

const LIST_FRAMES: &str = r#"<top> <k> 0 </k> <stack> <cur> <x> 0 </x> </cur> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </stack> </top>"#;

// The instances of a `type="List"` cell are ordered, and the order is part of what the rule
// matches. The <fr> lifted out of <cur> has no written position among the other <fr> cells of
// its <stack>: <cur> and <fr> are of different sorts, whose written order carries no meaning.
#[test]
fn rejects_a_misplaced_list_cell_whose_position_among_written_instances_is_unstated() {
    for rule in [
        "<stack> <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> <fr> <v> 1 </v> </fr> </stack>",
        "<stack> <fr> <v> 1 </v> </fr> <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> </stack>",
    ] {
        let errors = concretized_cell_rule(LIST_FRAMES, rule).unwrap_err();
        assert_eq!(
            errors,
            [
                "Cell <fr> written inside <cur> belongs in the <stack> that holds <cur>, whose <fr> cells form a list, and the rule does not state its position among the other items of that list"
            ],
            "{rule}"
        );
    }
}

// Two <fr> cells written as siblings in <cur> have a stated order, which they keep.
#[test]
fn places_misplaced_list_cells_lifted_out_of_one_parent_in_their_written_order() {
    let body = concretized_cell_rule(
        LIST_FRAMES,
        "<stack> <cur> <x> X </x> <fr> <v> 2 </v> </fr> <fr> <v> 3 </v> </fr> </cur> ... </stack>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<stack>`(`<cur>`(`<x>`(X)),`_FrCellList_`(`_FrCellList_`(`<fr>`(`<v>`(#token("2","Int"))),`<fr>`(`<v>`(#token("3","Int")))),_DotVar2))),_DotVar0)"#
    );
}

// The <fr> lifted out of <y>, which rides out of <cur> with <y>, and the one lifted out of <cur>
// were not written as siblings, so their order is not stated.
#[test]
fn rejects_misplaced_list_cells_lifted_out_of_different_parents_into_one_instance() {
    let errors = concretized_cell_rule(
        r#"<top> <k> 0 </k> <stack> <cur> <x> 0 </x> <y> <z> 0 </z> </y> </cur> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </stack> </top>"#,
        "<stack> <cur> <y> <z> Z </z> <fr> <v> 3 </v> </fr> </y> <fr> <v> 2 </v> </fr> ... </cur> ... </stack>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <fr> written inside <y> belongs in the <stack> that holds <y>, whose <fr> cells form a list, and the rule does not state its position among the other items of that list"
        ]
    );
}

#[test]
fn places_a_misplaced_list_cell_that_is_the_only_instance_written_in_its_parent() {
    let body = concretized_cell_rule(
        LIST_FRAMES,
        "<stack> <cur> <x> X => 1 </x> <fr> <v> 2 </v> </fr> </cur> ... </stack>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<stack>`(`<cur>`(`<x>`(X=>#token("1","Int"))),`_FrCellList_`(`<fr>`(`<v>`(#token("2","Int"))),_DotVar2))),_DotVar0)"#
    );
}

// Bag instances are unordered, so the lifted <fr> is placed beside the written one.
#[test]
fn places_a_misplaced_bag_cell_beside_written_instances() {
    let body = concretized_cell_rule(
        &LIST_FRAMES.replace(r#"type="List""#, r#"type="Bag""#),
        "<stack> <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> <fr> <v> 1 </v> </fr> </stack>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<stack>`(`<cur>`(`<x>`(X)),`_FrCellBag_`(`<fr>`(`<v>`(#token("1","Int"))),`<fr>`(`<v>`(#token("2","Int")))))),_DotVar0)"#
    );
}

const BESIDE_PARENT: &str = "<top> <a> <x> 0 </x> </a> <c> <d> 0 </d> <e> 0 </e> </c> </top>";

// <top> has one <c>, so a <d> written beside the written <c> is inside that <c>.
#[test]
fn places_a_cell_written_beside_its_only_possible_parent_inside_it() {
    let body = concretized_cell_rule(
        BESIDE_PARENT,
        "<a> <x> X </x> </a> <d> 5 => 6 </d> <c> <e> 1 </e> ... </c>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<a>`(`<x>`(X)),`<c>`(`<d>`(#token("5","Int")=>#token("6","Int")),`<e>`(#token("1","Int")))),_DotVar0)"#
    );
}

// The <c> written beside <d> is completed again with <d>, which goes into the <m> written in it.
#[test]
fn places_a_cell_written_beside_its_only_possible_ancestor_in_the_closest_written_one() {
    let body = concretized_cell_rule(
        "<top> <a> <x> 0 </x> </a> <c> <m> <d> 0 </d> <n> 0 </n> </m> <e> 0 </e> </c> </top>",
        "<a> <x> X </x> </a> <d> 5 => 6 </d> <c> <m> <n> 1 </n> ... </m> ... </c>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(`<a>`(`<x>`(X)),`<c>`(`<m>`(`<d>`(#token("5","Int")=>#token("6","Int")),`<n>`(#token("1","Int"))),_DotVar2)),_DotVar0)"#
    );
}

#[test]
fn rejects_a_cell_written_beside_its_only_possible_parent_written_closed() {
    let errors = concretized_cell_rule(
        BESIDE_PARENT,
        "<a> <x> X </x> </a> <d> 5 => 6 </d> <c> <e> 1 </e> </c>",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <d> written beside <c> belongs inside it: the configuration allows only one <c> there, and it is written closed (without ...), so it has no other children"
        ]
    );
}

// The written <c> is a rewrite: adding <d> to it would put <d> on both of its sides.
#[test]
fn rejects_a_cell_written_beside_its_only_possible_parent_written_as_a_rewrite() {
    let errors = concretized_cell_rule(
        BESIDE_PARENT,
        "<a> <x> X </x> </a> <d> 5 </d> (<c> <e> 1 </e> ... </c> => <c> <e> 2 </e> ... </c>)",
    )
    .unwrap_err();
    assert_eq!(
        errors,
        [
            "Cell <d> written beside <c> belongs inside it: the configuration allows only one <c> there, and that <c> is not written as a cell body <d> can be added to"
        ]
    );
}

// The <fr> written beside the one <stack> belongs in that <stack>'s list of <fr> cells, but the
// rule does not state its position relative to the <fr> cells written inside <stack>: they were
// not written as siblings in one body, and the text order of <stack> and <fr> carries no meaning.
#[test]
fn rejects_a_list_cell_written_beside_its_only_possible_parent_holding_written_instances() {
    for rule in [
        "<stack> <fr> <v> 1 </v> </fr> ... </stack> <fr> <v> 2 </v> </fr>",
        "<fr> <v> 2 </v> </fr> <stack> <fr> <v> 1 </v> </fr> ... </stack>",
        "<stack> <fr> <v> 1 </v> </fr> ... </stack> (.Bag => <fr> <v> 2 </v> </fr>)",
        "<fr> <v> 0 </v> </fr> <stack> <fr> <v> 1 </v> </fr> ... </stack> <fr> <v> 2 </v> </fr>",
    ] {
        let errors = concretized_cell_rule(LIST_FRAMES, rule).unwrap_err();
        assert_eq!(
            errors,
            [
                "Cell <fr> written beside <stack> belongs inside it: the configuration allows only one <stack> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list"
            ],
            "{rule}"
        );
    }
}

// The <fr> lifted out of <cur> is in <stack>'s list; the one written beside <stack> has no stated
// position relative to it.
#[test]
fn rejects_a_list_cell_written_beside_its_only_possible_parent_holding_a_lifted_instance() {
    for rule in [
        "<stack> <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> ... </stack> <fr> <v> 1 </v> </fr>",
        "<fr> <v> 1 </v> </fr> <stack> <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> ... </stack>",
    ] {
        let errors = concretized_cell_rule(LIST_FRAMES, rule).unwrap_err();
        assert_eq!(
            errors,
            [
                "Cell <fr> written beside <stack> belongs inside it: the configuration allows only one <stack> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list (after moving <fr> written inside <cur> to where the configuration declares it)"
            ],
            "{rule}"
        );
    }
}

// A variable of an unknown cell sort in <stack> may stand for <fr> cells of its list, so neither
// a <fr> written beside <stack> nor one lifted out of <cur> has a stated position.
#[test]
fn rejects_a_list_cell_placed_beside_a_term_of_unknown_cell_sort() {
    for (rule, written) in [
        (
            "<stack> <cur> <x> X </x> </cur> F:Bag ... </stack> <fr> <v> 2 </v> </fr>",
            "Cell <fr> written beside <stack> belongs inside it: the configuration allows only one <stack> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        ),
        (
            "<stack> <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> F:Bag ... </stack>",
            "Cell <fr> written inside <cur> belongs in the <stack> that holds <cur>, whose <fr> cells form a list, and the rule does not state its position among the other items of that list",
        ),
    ] {
        let errors = concretized_cell_rule(LIST_FRAMES, rule).unwrap_err();
        assert_eq!(errors, [written], "{rule}");
    }
}

const NESTED_LIST_FRAMES: &str = r#"<top> <k> 0 </k> <a> <z> 0 </z> <p> <y> 0 </y> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </p> </a> </top>"#;

// The <fr> written beside <a> belongs in the one <p> of the one <a>, whose list already holds the
// <fr> written in <a> (directly, or moved into the <p> written there).
#[test]
fn rejects_a_list_cell_written_beside_its_only_possible_ancestor_holding_written_instances() {
    for rule in [
        "<a> <fr> <v> 1 </v> </fr> ... </a> <fr> <v> 2 </v> </fr>",
        "<a> <p> <y> 1 </y> ... </p> <fr> <v> 1 </v> </fr> ... </a> <fr> <v> 2 </v> </fr>",
    ] {
        let errors = concretized_cell_rule(NESTED_LIST_FRAMES, rule).unwrap_err();
        assert_eq!(
            errors,
            [
                "Cell <fr> written beside <a> belongs inside it: the configuration allows only one <a> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list"
            ],
            "{rule}"
        );
    }
}

// With no other item of its list in <stack>, the <fr> written beside <stack> is placed as a <fr>
// written alone inside it would be.
#[test]
fn places_a_list_cell_written_beside_its_only_possible_parent_holding_no_other_instance() {
    let body = concretized_cell_rule(
        LIST_FRAMES,
        "<stack> <cur> <x> X </x> </cur> ... </stack> <fr> <v> 2 </v> </fr>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<stack>`(`<cur>`(`<x>`(X)),`_FrCellList_`(`<fr>`(`<v>`(#token("2","Int"))),_DotVar2))),_DotVar0)"#
    );
}

// Two <fr> cells written as siblings beside <stack> keep their written order.
#[test]
fn places_list_cells_written_beside_their_only_possible_parent_in_their_written_order() {
    let body = concretized_cell_rule(
        LIST_FRAMES,
        "<fr> <v> 0 </v> </fr> <stack> <cur> <x> X </x> </cur> ... </stack> <fr> <v> 2 </v> </fr>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<stack>`(`<cur>`(`<x>`(X)),`_FrCellList_`(`_FrCellList_`(`<fr>`(`<v>`(#token("0","Int"))),`<fr>`(`<v>`(#token("2","Int")))),_DotVar2))),_DotVar0)"#
    );
}

// The <fr> goes into the <a> written beside it and then into the <p> written in that <a>.
#[test]
fn places_a_list_cell_written_beside_its_only_possible_ancestor_in_the_written_parent() {
    let body = concretized_cell_rule(
        NESTED_LIST_FRAMES,
        "<a> <p> <y> 1 </y> ... </p> ... </a> <fr> <v> 2 </v> </fr>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<a>`(_DotVar2,`<p>`(`<y>`(#token("1","Int")),`_FrCellList_`(`<fr>`(`<v>`(#token("2","Int"))),_DotVar3)))),_DotVar0)"#
    );
}

// Bag instances are unordered, so the <fr> written beside <stack> joins the written one.
#[test]
fn places_a_bag_cell_written_beside_its_only_possible_parent_beside_written_instances() {
    let body = concretized_cell_rule(
        &LIST_FRAMES.replace(r#"type="List""#, r#"type="Bag""#),
        "<stack> <fr> <v> 1 </v> </fr> ... </stack> <fr> <v> 2 </v> </fr>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<stack>`(_Gen3,`_FrCellBag_`(`_FrCellBag_`(`<fr>`(`<v>`(#token("1","Int"))),`<fr>`(`<v>`(#token("2","Int")))),_Gen4))),_DotVar0)"#
    );
}

// <top> holds one <threads>, and that <threads> holds many <thread> cells; likewise for the
// <d> of some <a2> in some <r> of the one <a>. A cell written beside the one <threads> (or <a>)
// states nothing its spelling inside that cell does not, so it is moved there and both spellings
// are one rule. Inside it the written <thread> (or the <r> of the written <a2>) may hold the
// moved cell, as may another instance, and the rule does not state which: both spellings are
// rejected alike, naming the cell, the repeated cell and the written instance.
#[test]
fn rejects_a_cell_beside_its_only_possible_ancestor_through_a_repeated_cell_as_inside_it() {
    for (configuration, beside, inside, error) in [
        (
            r#"<top> <k> 0 </k> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <env> 0 </env> </thread> </threads> </top>"#,
            "<k> 0 => 1 </k> <threads> <thread> <id> 1 </id> ... </thread> ... </threads> <env> E => 0 </env>",
            "<k> 0 => 1 </k> <threads> <thread> <id> 1 </id> ... </thread> <env> E => 0 </env> ... </threads>",
            "Ambiguous completion: <env>, written outside every <thread>, can be in the written <thread> (holding <id>) or in another <thread>, and the rule does not state which; write <env> inside the <thread> that holds it",
        ),
        (
            r#"<top> <k> 0 </k> <threads> <thread multiplicity="*" type="List"> <id> 0 </id> <env> 0 </env> </thread> </threads> </top>"#,
            "<k> 0 => 1 </k> <threads> <thread> <id> 1 </id> ... </thread> ... </threads> <env> E </env>",
            "<k> 0 => 1 </k> <threads> <thread> <id> 1 </id> ... </thread> <env> E </env> ... </threads>",
            "Ambiguous completion: <env>, written outside every <thread>, can be in the written <thread> (holding <id>) or in another <thread>, and the rule does not state which; write <env> inside the <thread> that holds it",
        ),
        (
            r#"<top> <k> 0 </k> <a> <x> 0 </x> <r multiplicity="*" type="Map"> <rid> 0 </rid> <a2> <y> 0 </y> <d> 0 </d> </a2> </r> </a> </top>"#,
            "<k> 0 => 1 </k> <a> <x> X </x> ... </a> <a2> <y> 1 </y> ... </a2> <d> 5 => 6 </d>",
            "<k> 0 => 1 </k> <a> <x> X </x> <a2> <y> 1 </y> ... </a2> <d> 5 => 6 </d> ... </a>",
            "Ambiguous completion: <d>, written outside every <a2>, can be in the <r> of the written <a2> (holding <y>) or in another <r>, and the rule does not state which; write <d> inside the <a2> that holds it",
        ),
    ] {
        let placed = concretized_cell_rule(configuration, beside);
        assert_eq!(placed, Err(vec![error.to_owned()]), "{beside}");
        assert_eq!(
            placed,
            concretized_cell_rule(configuration, inside),
            "{inside}"
        );
    }
}

const LIST_BESIDE_REWRITE: &str = r#"<top> <k> 0 </k> <stack> <sp> 0 </sp> <c1> <x> 0 </x> </c1> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </stack> </top>"#;

// The rewrite in <stack> is of <sp> cells on both sides, but its Bag variable B may stand for <fr>
// cells of <stack>'s list, so the <fr> moved into <stack> (written beside it) or lifted into it
// (written inside <c1>) has no stated position relative to B's cells.
#[test]
fn rejects_a_list_cell_placed_beside_a_rewrite_holding_a_term_of_unknown_cell_sort() {
    for (rule, written) in [
        (
            "<k> 0 => 1 </k> <stack> (<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag) <c1> <x> X </x> </c1> ... </stack> <fr> <v> 2 </v> </fr>",
            "Cell <fr> written beside <stack> belongs inside it: the configuration allows only one <stack> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        ),
        (
            "<k> 0 => 1 </k> <stack> (<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag) <c1> <x> X </x> <fr> <v> 2 </v> </fr> </c1> ... </stack>",
            "Cell <fr> written inside <c1> belongs in the <stack> that holds <c1>, whose <fr> cells form a list, and the rule does not state its position among the other items of that list",
        ),
    ] {
        let errors = concretized_cell_rule(LIST_BESIDE_REWRITE, rule).unwrap_err();
        assert_eq!(errors, [written], "{rule}");
    }
}

const LIST_ITEMS: &str = r#"<top> <k> 0 </k> <stack> <sp> 0 </sp> <cur> <x> 0 </x> </cur> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </stack> </top>"#;

const LIST_ITEM_SYNTAX: &str = "syntax Bag ::= bag(Int) [function]
          syntax SpCell ::= sp(Int) [function]
          syntax FrCell ::= fr(Int) [function]";

// Every shape an item of a cell body can have after parsing (a cell, a variable, a rewrite, an
// alias, an empty bag, a function application, which a left side may not hold outside a rewrite),
// each written in <stack> beside a <fr> placed there, with whether it may be or hold an instance
// of <stack>'s list of <fr> cells. A term of unknown cell sort may (the <fr> slot of <stack> is
// `multiplicity="*"`, so always free); a rewrite or an alias may if any part of it may. (An alias
// of several cells is rejected by child ordering, whatever it holds.)
const LIST_ITEM_SHAPES: &[(&str, bool)] = &[
    ("<fr> <v> 1 </v> </fr>", true),
    ("(<fr> <v> 1 </v> </fr> => .Bag)", true),
    ("(.Bag => <fr> <v> 1 </v> </fr>)", true),
    ("(<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag)", true),
    ("(<sp> S </sp> => <sp> S </sp> B:Bag)", true),
    ("(<sp> S </sp> <fr> <v> 1 </v> </fr> => <sp> 1 </sp>)", true),
    ("(<fr> <v> 1 </v> </fr> #as F:FrCell)", true),
    ("B:Bag", true),
    ("F:FrCell", true),
    ("(<sp> S </sp> => <sp> S </sp> bag(1))", true),
    ("(.Bag => fr(1))", true),
    ("(<sp> S </sp> => <sp> 1 </sp>)", false),
    ("(<sp> S </sp> => sp(1))", false),
    ("<sp> S </sp>", false),
    ("P:SpCell", false),
    (".Bag", false),
];

fn assert_list_cell_placed_or_rejected(rule: &str, in_list: bool, rejection: &str) {
    let result = concretized_cell_rule_in(LIST_ITEM_SYNTAX, LIST_ITEMS, rule, "");
    if in_list {
        assert_eq!(result.unwrap_err(), [rejection], "{rule}");
    } else {
        let body = result.unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
        // The placed <fr> is the only stated item of the list, followed by the rest of it.
        assert!(
            body.contains(r#"`_FrCellList_`(`<fr>`(`<v>`(#token("2","Int"))),_"#),
            "{rule}: {body}"
        );
    }
}

#[test]
fn places_a_list_cell_written_beside_its_only_possible_parent_only_beside_items_outside_its_list() {
    for (item, in_list) in LIST_ITEM_SHAPES {
        assert_list_cell_placed_or_rejected(
            &format!("<stack> {item} <cur> <x> X </x> </cur> ... </stack> <fr> <v> 2 </v> </fr>"),
            *in_list,
            "Cell <fr> written beside <stack> belongs inside it: the configuration allows only one <stack> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        );
    }
}

#[test]
fn places_a_misplaced_list_cell_lifted_into_its_parent_only_beside_items_outside_its_list() {
    for (item, in_list) in LIST_ITEM_SHAPES {
        assert_list_cell_placed_or_rejected(
            &format!("<stack> {item} <cur> <x> X </x> <fr> <v> 2 </v> </fr> </cur> ... </stack>"),
            *in_list,
            "Cell <fr> written inside <cur> belongs in the <stack> that holds <cur>, whose <fr> cells form a list, and the rule does not state its position among the other items of that list",
        );
    }
}

// A cell of another sort moved or lifted into <stack> is part of its <fr> list when it may hold
// <fr> cells: here a rewrite of <sp> cells whose Bag variable may stand for some.
#[test]
fn rejects_a_term_holding_list_cells_placed_beside_written_instances() {
    for (rule, written) in [
        (
            "<stack> <fr> <v> 1 </v> </fr> <cur> <x> X </x> </cur> ... </stack> (<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag)",
            "Cell <sp> written beside <stack> belongs inside it: the configuration allows only one <stack> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        ),
        (
            "<stack> <fr> <v> 1 </v> </fr> <cur> <x> X </x> (<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag) </cur> ... </stack>",
            "Cell <sp> written inside <cur> belongs in the <stack> that holds <cur>, whose <fr> cells form a list, and the rule does not state its position among the other items of that list",
        ),
    ] {
        let errors = concretized_cell_rule(LIST_ITEMS, rule).unwrap_err();
        assert_eq!(errors, [written], "{rule}");
    }
    // Without a <fr> written in <stack>, B's cells are the list's only stated items.
    for rule in [
        "<stack> <cur> <x> X </x> </cur> ... </stack> (<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag)",
        "<stack> <cur> <x> X </x> (<sp> S </sp> B:Bag => <sp> 1 </sp> B:Bag) </cur> ... </stack>",
    ] {
        concretized_cell_rule(LIST_ITEMS, rule)
            .unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
    }
}

// The <fr> written beside <a> goes into the one <p> of the one <a>. Only what that <p> may hold
// can be part of its list; the frame of the written <p> is the rest of the list, after the placed
// <fr>, as for a <fr> written in it.
#[test]
fn places_a_list_cell_written_beside_its_only_possible_ancestor_only_beside_items_outside_its_list()
{
    for (item, in_list) in [
        ("<p> <y> 1 </y> ... </p>", false),
        ("<p> ... <y> 1 </y> </p>", false),
        ("<z> Z </z>", false),
        ("<p> <fr> <v> 1 </v> </fr> ... </p>", true),
        ("<p> B:Bag ... </p>", true),
        ("<p> (<y> Y </y> B:Bag => <y> 1 </y> B:Bag) ... </p>", true),
        ("(<p> <y> 1 </y> ... </p> => <p> <y> 2 </y> ... </p>)", true),
        (
            "(<p> <y> 1 </y> <fr> <v> 1 </v> </fr> </p> => <p> <y> 2 </y> </p>)",
            true,
        ),
        ("P:PCell", true),
        ("B:Bag", true),
    ] {
        let rule = format!("<a> {item} ... </a> <fr> <v> 2 </v> </fr>");
        let result = concretized_cell_rule(NESTED_LIST_FRAMES, &rule);
        if in_list {
            assert_eq!(
                result.unwrap_err(),
                [
                    "Cell <fr> written beside <a> belongs inside it: the configuration allows only one <a> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list"
                ],
                "{rule}"
            );
        } else {
            let body = result.unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
            assert!(
                body.contains(r#"`_FrCellList_`(`<fr>`(`<v>`(#token("2","Int"))),_"#),
                "{rule}: {body}"
            );
        }
    }
}

// The <p> moved into <a> brings its own list of <fr> cells, stated by its body: nothing else in
// <a> can be part of that list.
#[test]
fn places_a_cell_above_a_list_written_beside_its_only_possible_parent_with_its_list() {
    for rule in [
        "<a> <z> Z </z> B:Bag ... </a> <p> <fr> <v> 1 </v> </fr> ... </p>",
        "<a> <z> Z </z> ... </a> <p> <fr> <v> 1 </v> </fr> ... </p>",
    ] {
        let body = concretized_cell_rule(NESTED_LIST_FRAMES, rule)
            .unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
        assert!(
            body.contains(r#"`_FrCellList_`(`<fr>`(`<v>`(#token("1","Int"))),_"#),
            "{rule}: {body}"
        );
    }
}

const LIST_BESIDE_SIBLINGS: &str = r#"<top> <k> 0 </k> <a> <x> 0 </x> <z> 0 </z> <p> <y> 0 </y> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </p> </a> </top>"#;

const REPEATED_LIST_PARENTS: &str = r#"<top> <k> 0 </k> <a> <z> 0 </z> <w> <u> 0 </u> </w> <p multiplicity="*" type="Map"> <pid> 0 </pid> <fr multiplicity="*" type="List"> <v> 0 </v> </fr> </p> </a> </top>"#;

// After completion <c1> holds only its own children, so neither the Bag variable in its body nor a
// rewrite holding one can be part of <stack>'s list of <fr> cells; and in <a>, whose one <p> is
// written, the Bag variable of the <z> rewrite moved into <a> stands for children of <a> other
// than that <p>, so it cannot be part of the <p>'s list either. Each rule, with a <fr> written
// beside <stack> or inside <c1>, or a rewrite written beside <a>, is the rule written with that
// cell in place, and compiles to it.
#[test]
fn places_a_cell_beside_terms_of_unknown_cell_sort_that_cannot_reach_its_list() {
    for (configuration, rule, written) in [
        (
            LIST_BESIDE_REWRITE,
            "<k> 0 => 1 </k> <stack> <sp> S </sp> <c1> <x> X </x> B:Bag </c1> ... </stack> <fr> <v> 2 </v> </fr>",
            "<k> 0 => 1 </k> <stack> <sp> S </sp> <c1> <x> X </x> B:Bag </c1> <fr> <v> 2 </v> </fr> ... </stack>",
        ),
        (
            LIST_BESIDE_REWRITE,
            "<k> 0 => 1 </k> <stack> <sp> S </sp> <c1> <x> X </x> B:Bag <fr> <v> 2 </v> </fr> </c1> ... </stack>",
            "<k> 0 => 1 </k> <stack> <sp> S </sp> <c1> <x> X </x> B:Bag </c1> <fr> <v> 2 </v> </fr> ... </stack>",
        ),
        (
            LIST_BESIDE_REWRITE,
            "<k> 0 => 1 </k> <stack> <sp> S </sp> <c1> (<x> X </x> B:Bag => <x> 1 </x> B:Bag) </c1> ... </stack> <fr> <v> 2 </v> </fr>",
            "<k> 0 => 1 </k> <stack> <sp> S </sp> <c1> (<x> X </x> B:Bag => <x> 1 </x> B:Bag) </c1> <fr> <v> 2 </v> </fr> ... </stack>",
        ),
        (
            NESTED_LIST_FRAMES,
            "<k> 0 => 1 </k> <a> <p> <fr> <v> 1 </v> </fr> ... </p> ... </a> (<z> Z </z> B:Bag => <z> 1 </z> B:Bag)",
            "<k> 0 => 1 </k> <a> <p> <fr> <v> 1 </v> </fr> ... </p> (<z> Z </z> B:Bag => <z> 1 </z> B:Bag) ... </a>",
        ),
        // The one <p> written on both sides of a rewrite is still the only one.
        (
            NESTED_LIST_FRAMES,
            "<k> 0 => 1 </k> <a> (<p> <fr> <v> 1 </v> </fr> ... </p> => <p> <fr> <v> 2 </v> </fr> ... </p>) ... </a> (<z> Z </z> B:Bag => <z> 1 </z> B:Bag)",
            "<k> 0 => 1 </k> <a> (<p> <fr> <v> 1 </v> </fr> ... </p> => <p> <fr> <v> 2 </v> </fr> ... </p>) (<z> Z </z> B:Bag => <z> 1 </z> B:Bag) ... </a>",
        ),
        // The Bag variable of the <u> rewrite stands for children of <w>, none above <fr>, whatever
        // <a> holds: here many <p> cells, each with its own list.
        (
            REPEATED_LIST_PARENTS,
            "<k> 0 => 1 </k> <a> <z> Z </z> <p> <pid> 1 </pid> <fr> <v> 1 </v> </fr> ... </p> ... </a> (<u> U </u> B:Bag => <u> 1 </u> B:Bag)",
            "<k> 0 => 1 </k> <a> <z> Z </z> <p> <pid> 1 </pid> <fr> <v> 1 </v> </fr> ... </p> (<u> U </u> B:Bag => <u> 1 </u> B:Bag) ... </a>",
        ),
        // The one <p> arrives in <a> only with the cells moved there, beside the <z> rewrite: it
        // is still the only one, and B (unlike B2, already in <a>) cannot stand for another.
        (
            LIST_BESIDE_SIBLINGS,
            "<k> 0 => 1 </k> <a> <x> X </x> B2:Bag ... </a> <p> <fr> <v> 1 </v> </fr> ... </p> (<z> Z </z> B:Bag => <z> 1 </z> B:Bag)",
            "<k> 0 => 1 </k> <a> <x> X </x> B2:Bag <p> <fr> <v> 1 </v> </fr> ... </p> (<z> Z </z> B:Bag => <z> 1 </z> B:Bag) ... </a>",
        ),
    ] {
        let placed = concretized_cell_rule(configuration, rule)
            .unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
        let in_place = concretized_cell_rule(configuration, written)
            .unwrap_or_else(|errors| panic!("{written}: {errors:?}"));
        assert_eq!(placed, in_place, "{rule}");
    }
}

// A Bag variable moved into <a> may still be part of a list: when the child of <a> on the way to
// the list is not written in <a> (a <y> rewrite would go into a fresh <p>, beside whatever F
// stands for), or is written on one side of a rewrite only (B may stand for a <p> on the other
// side), or when the variable reaches the list's own parent (the <y> rewrite goes into the
// written <p>, where B may stand for <fr> cells beside the written one).
#[test]
fn rejects_a_moved_term_of_unknown_cell_sort_that_may_reach_a_list() {
    for (rule, written) in [
        (
            "<k> 0 => 1 </k> <a> <z> Z </z> F:Bag ... </a> (<y> Y </y> B:Bag => <y> 1 </y> B:Bag)",
            "Cell <y> written beside <a> belongs inside it: the configuration allows only one <a> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        ),
        (
            "<k> 0 => 1 </k> <a> (.Bag => <p> <fr> <v> 1 </v> </fr> ... </p>) ... </a> (<z> Z </z> B:Bag => <z> 1 </z> B:Bag)",
            "Cell <z> written beside <a> belongs inside it: the configuration allows only one <a> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        ),
        (
            "<k> 0 => 1 </k> <a> <p> <fr> <v> 1 </v> </fr> ... </p> ... </a> (<y> Y </y> B:Bag => <y> 1 </y> B:Bag)",
            "Cell <y> written beside <p> belongs inside it: the configuration allows only one <p> there, the <fr> cells in it form a list, and the rule does not state its position among the other items of that list",
        ),
    ] {
        let errors = concretized_cell_rule(NESTED_LIST_FRAMES, rule).unwrap_err();
        assert_eq!(errors, [written], "{rule}");
    }
}

// <a> is the only <a>, so the <d> written beside it is in it, in some <r> of it: what the rule
// states when <d> is written inside <a> (the second spelling), or inside an <r> written beside
// <a> (the third). <a> holds no other <r> the <d> could be in, and <r>'s collection is
// commutative, so the fresh <r> completion builds around <d> is that "some <r>". All three
// spellings compile to one rule.
#[test]
fn places_a_cell_written_beside_its_only_possible_ancestor_in_a_fresh_commutative_instance() {
    for collection in ["Map", "Set"] {
        let configuration = format!(
            r#"<top> <k> 0 </k> <a> <x> 0 </x> <r multiplicity="*" type="{collection}"> <rid> 0 </rid> <d> 0 </d> </r> </a> </top>"#
        );
        let bodies = [
            "<a> <x> X </x> ... </a> <d> 5 => 6 </d>",
            "<a> <x> X </x> <d> 5 => 6 </d> ... </a>",
            "<a> <x> X </x> ... </a> <r> <d> 5 => 6 </d> ... </r>",
        ]
        .map(|rule| {
            concretized_cell_rule(&configuration, rule)
                .unwrap_or_else(|errors| panic!("{rule}: {errors:?}"))
        });
        assert_eq!(bodies[0], bodies[1], "{collection}");
        assert_eq!(bodies[0], bodies[2], "{collection}");
        // With a <p> between <a> and <r>, the fresh <r> is built in the one <p> of <a>, written
        // or not, beside that <p>'s `...`, which stands for its other children (other <r> cells
        // among them) and is not an <r> the <d> could be in.
        let configuration = format!(
            r#"<top> <k> 0 </k> <a> <x> 0 </x> <p> <y> 0 </y> <r multiplicity="*" type="{collection}"> <rid> 0 </rid> <d> 0 </d> <e> 0 </e> </r> </p> </a> </top>"#
        );
        for (rule, written) in [
            (
                "<a> <x> X </x> ... </a> <d> 5 => 6 </d>",
                "<a> <x> X </x> <d> 5 => 6 </d> ... </a>",
            ),
            (
                "<a> <p> <y> 1 </y> ... </p> ... </a> <d> 5 => 6 </d>",
                "<a> <p> <y> 1 </y> <d> 5 => 6 </d> ... </p> ... </a>",
            ),
            (
                "<a> <x> X </x> ... </a> <p> <y> 1 </y> ... </p> <d> 5 => 6 </d>",
                "<a> <x> X </x> <p> <y> 1 </y> <d> 5 => 6 </d> ... </p> ... </a>",
            ),
        ] {
            let placed = concretized_cell_rule(&configuration, rule)
                .unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
            let in_place = concretized_cell_rule(&configuration, written)
                .unwrap_or_else(|errors| panic!("{written}: {errors:?}"));
            assert_eq!(placed, in_place, "{collection}: {rule}");
        }
    }
    let body = concretized_cell_rule(
        r#"<top> <k> 0 </k> <a> <x> 0 </x> <r multiplicity="*" type="Map"> <rid> 0 </rid> <d> 0 </d> </r> </a> </top>"#,
        "<a> <x> X </x> ... </a> <d> 5 => 6 </d>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<a>`(`<x>`(X),`_RCellMap_`(`<r>`(_DotVar3,`<d>`(#token("5","Int")=>#token("6","Int"))),_DotVar2))),_DotVar0)"#
    );
}

// The <d> written beside the one <a> is moved into it whatever <a> holds: a written <r>, a
// variable that may stand for <r> cells, another cell moved into <a> with <d>, or a List <r>. The
// rule is the one written with <d> inside <a>, compiled or rejected alike. With a List <r> and no
// other item of the list in <a>, the fresh <r> holding <d> is the only item written in the list
// and is placed before the rest of it.
#[test]
fn compiles_a_cell_beside_its_only_possible_ancestor_as_inside_it_whatever_the_ancestor_holds() {
    let map = r#"<top> <k> 0 </k> <a> <x> 0 </x> <w> <u> 0 </u> </w> <r multiplicity="*" type="Map"> <rid> 0 </rid> <d> 0 </d> </r> </a> </top>"#;
    let list = r#"<top> <k> 0 </k> <a> <x> 0 </x> <r multiplicity="*" type="List"> <d> 0 </d> </r> </a> </top>"#;
    for (configuration, beside, inside) in [
        (
            map,
            "<a> <x> X </x> <r> <rid> 1 </rid> ... </r> ... </a> <d> 5 => 6 </d>",
            "<a> <x> X </x> <r> <rid> 1 </rid> ... </r> <d> 5 => 6 </d> ... </a>",
        ),
        (
            map,
            "<a> <x> X </x> B:Bag ... </a> <d> 5 => 6 </d>",
            "<a> <x> X </x> B:Bag <d> 5 => 6 </d> ... </a>",
        ),
        (
            map,
            "<a> <x> X </x> ... </a> <r> <rid> 1 </rid> ... </r> <d> 5 => 6 </d>",
            "<a> <x> X </x> <r> <rid> 1 </rid> ... </r> <d> 5 => 6 </d> ... </a>",
        ),
        (
            map,
            "<a> <x> X </x> ... </a> <w> <u> 1 </u> <r> <rid> 1 </rid> ... </r> </w> <d> 5 => 6 </d>",
            "<a> <x> X </x> <w> <u> 1 </u> <r> <rid> 1 </rid> ... </r> </w> <d> 5 => 6 </d> ... </a>",
        ),
        (
            list,
            "<a> <x> X </x> ... </a> <d> 5 => 6 </d>",
            "<a> <x> X </x> <d> 5 => 6 </d> ... </a>",
        ),
    ] {
        assert_eq!(
            concretized_cell_rule(configuration, beside),
            concretized_cell_rule(configuration, inside),
            "{beside}"
        );
    }
    let body = concretized_cell_rule(list, "<a> <x> X </x> ... </a> <d> 5 => 6 </d>").unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_DotVar1,`<a>`(`<x>`(X),`_RCellList_`(`<r>`(`<d>`(#token("5","Int")=>#token("6","Int"))),_DotVar2))),_DotVar0)"#
    );
}

// The <a> written in <top> is in one of many <r> cells, and the rule does not state whether the
// <d> written beside it is in that <r>: the written <a> may hold it (its <d> is free and its frame
// open), and so may an <a> in another <r>. The rule is rejected naming <d>, <r> and the written
// <a>, before the <s> is grouped. When the written <a> already holds a <d>, only another <r> can
// hold the loose one, which completion builds.
#[test]
fn rejects_a_cell_beside_its_written_ancestor_when_a_repeated_cell_lies_above_that_ancestor() {
    let configuration = r#"<top> <k> 0 </k> <r multiplicity="*" type="Map"> <rid> 0 </rid> <s> 0 </s> <a> <e> 0 </e> <d> 0 </d> </a> </r> </top>"#;
    for rule in [
        "<s> 1 </s> <a> <e> 1 </e> ... </a> <d> 5 => 6 </d>",
        "<a> <e> 1 </e> ... </a> <d> 5 => 6 </d>",
    ] {
        assert_eq!(
            concretized_cell_rule(configuration, rule),
            Err(vec!["Ambiguous completion: <d>, written outside every <a>, can be in the <r> of the written <a> (holding <e>) or in another <r>, and the rule does not state which; write <d> inside the <a> that holds it".to_owned()]),
            "{rule}"
        );
    }
    let body = concretized_cell_rule(
        configuration,
        "<a> <e> 1 </e> <d> D </d> ... </a> <d> 5 => 6 </d>",
    )
    .unwrap();
    assert_eq!(
        body,
        r#"`<generatedTop>`(`<top>`(_Gen6,`_RCellMap_`(`_RCellMap_`(`<r>`(_Gen8,_Gen9,`<a>`(`<e>`(#token("1","Int")),`<d>`(D))),`<r>`(_Gen10,_Gen11,`<a>`(_DotVar5,`<d>`(#token("5","Int")=>#token("6","Int"))))),_Gen7)),_DotVar0)"#
    );
}

// A written instance of the parent may stand inside a written cell above it: here the <a2>
// written in the written <r> may hold the <d> written outside every <a2> (its <d> is free and its
// frame open), and so may an <a2> in another <r>. Written beside the <r> or inside <a>, <d> is
// rejected as when the <a2> is written directly beside it. When that <a2> already holds a <d>, or
// the written <r> is removed, only another <r> can hold the loose <d>, which completion builds.
#[test]
fn rejects_a_cell_that_a_written_instance_inside_a_written_repeated_cell_may_hold() {
    let configuration = r#"<top> <k> 0 </k> <a> <x> 0 </x> <r multiplicity="*" type="Map"> <rid> 0 </rid> <a2> <y> 0 </y> <d> 0 </d> </a2> </r> </a> </top>"#;
    for rule in [
        "<k> 0 => 1 </k> <a> <r> <rid> 1 </rid> <a2> <y> 1 </y> ... </a2> ... </r> ... </a> <d> 5 => 6 </d>",
        "<k> 0 => 1 </k> <a> <r> <rid> 1 </rid> <a2> <y> 1 </y> ... </a2> ... </r> <d> 5 => 6 </d> ... </a>",
        "<k> 0 => 1 </k> <a> (<r> <rid> 1 </rid> <a2> <y> 1 </y> ... </a2> ... </r> => <r> <rid> 1 </rid> <a2> <y> 2 </y> ... </a2> ... </r>) ... </a> <d> 5 => 6 </d>",
    ] {
        let errors =
            concretized_cell_rule(configuration, rule).expect_err("the written <a2> may hold <d>");
        assert!(
            errors.iter().any(|error| error.starts_with("Ambiguous completion: <d>, written outside every <a2>, can be in the <r> of the written <a2> (holding <y>) or in another <r>")),
            "{rule}: {errors:?}"
        );
    }
    for rule in [
        "<k> 0 => 1 </k> <a> <r> <rid> 1 </rid> <a2> <y> 1 </y> <d> D </d> ... </a2> ... </r> ... </a> <d> 5 => 6 </d>",
        "<k> 0 => 1 </k> <a> (<r> <rid> 1 </rid> <a2> <y> 1 </y> ... </a2> ... </r> => .Bag) ... </a> <d> 5 => 6 </d>",
    ] {
        let body = concretized_cell_rule(configuration, rule)
            .unwrap_or_else(|errors| panic!("{rule}: {errors:?}"));
        assert_eq!(body.matches("`<r>`(").count(), 2, "{rule}: {body}");
    }
}

// Whether an item of <thread>'s sort written beside a loose <env> may be the <thread> that holds
// it, by the shape of that item. The <thread> completion builds for the <env> is on both sides of
// the rule, so an item may be it only when it is a <thread> on both sides that leaves <env> free on
// each, with a frame or a term of unknown cell sort to stand for it, or a term that stands for one
// whole <thread> (a variable of its sort). A term of unknown cell sort (a `Bag` variable, the
// frame) stands for any number of instances, and a built instance beside it already denotes the
// one among them that holds the <env>, so it is no other reading.
#[test]
fn rejects_a_loose_cell_only_where_a_written_instance_may_hold_it() {
    let configuration = r#"<top> <k> 0 </k> <threads> <thread multiplicity="*" type="Map"> <id> 0 </id> <env> 0 </env> <o> 0 </o> </thread> </threads> </top>"#;
    let mut failures = Vec::new();
    for (written, holder) in [
        (
            "<thread> <id> 1 </id> ... </thread>",
            Some("<thread> (holding <id>)"),
        ),
        (
            "(<thread> <id> 1 </id> ... </thread> #as T)",
            Some("<thread> (holding <id>) #as T"),
        ),
        ("T:ThreadCell", Some("<thread> T")),
        (
            "<thread> <id> 1 </id> <o> 0 </o> B:Bag </thread>",
            Some("<thread> (holding an item <id> <o>)"),
        ),
        (
            "(<thread> <id> 1 </id> ... </thread> => <thread> <id> 2 </id> ... </thread>)",
            Some("<thread> (holding <id>)"),
        ),
        ("<thread> <id> 1 </id> <env> X </env> ... </thread>", None),
        (
            "<thread> <id> 1 </id> <env> X </env> <o> 0 </o> </thread>",
            None,
        ),
        ("(<thread> <id> 1 </id> ... </thread> => .Bag)", None),
        ("(.Bag => <thread> <id> 1 </id> ... </thread>)", None),
        ("B:Bag", None),
    ] {
        let rule = format!("<threads> {written} ... </threads> <env> E => 0 </env>");
        let outcome = concretized_cell_rule(configuration, &rule);
        let expected = holder.map(|holder| {
            vec![format!(
                "Ambiguous completion: <env>, written outside every <thread>, can be in the written {holder} or in another <thread>, and the rule does not state which; write <env> inside the <thread> that holds it"
            )]
        });
        let agrees = match (&outcome, expected) {
            (Ok(_), None) => true,
            (Err(errors), Some(expected)) => *errors == expected,
            _ => false,
        };
        if !agrees {
            failures.push(format!("\n  {written}\n    -> {outcome:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join(""));
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
    let definition = resolve_semantic_casts(&parsed(&source)).unwrap();
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
            .find_map(
                |sentence| match k_rust::definition::sentence_mut(sentence) {
                    Sentence::Rule {
                        body, attributes, ..
                    } if attributes.get("initializer").is_none() => Some(body),
                    _ => None,
                },
            )
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
            .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();

    for sentence in transformed
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        let Sentence::Rule { body, .. } = &**sentence else {
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
    let transformed = generate_sort_predicate_rules(&transformed).unwrap();
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&definition).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&definition).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let mut definition = resolve_fresh_constants(&definition, 0).unwrap();
    let open_thread = incomplete_cell("<thread>", application("#cells", Vec::new()));
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .push(
            rule(
                rewrite(
                    application(".Bag", Vec::new()),
                    application("#cells", vec![open_thread.clone(), open_thread]),
                ),
                attributes(&[("label", json!("equal-defaults"))]),
            )
            .into(),
        );
    let transformed = concretize_cells(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
                    .map(|destination| (destination.path.to_vec(), destination.sentence_index)),
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
            let definition = resolve_semantic_casts(&parsed(&source)).unwrap();
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
                .find_map(|sentence| match &**sentence {
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
        module BOOL
        endmodule
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let output = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
    let definition = number_sentences(&generate_sort_predicate_rules(&definition).unwrap());
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
        .filter_map(|sentence| match &**sentence {
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

/// `#Layout` is parser scaffolding, not a set of K terms, so compilation declares no sort
/// predicate for it even when the main module declares it, and nothing injects it into `K`; the
/// defined sort next to it keeps its predicate.
/// A sort whose predicate exists but which is not placeable at `K` in its module gets only the
/// `owise` rule `isS(K) => false`: no term of the sort can be the `K` argument. Of the roles with
/// a predicate, only `KConfigVar` is not below `KItem` by its role, so it is the one sort that can
/// reach this branch: in a module that declares it without `syntax KItem ::= KConfigVar`.
#[test]
fn an_unplaceable_sort_with_a_predicate_keeps_only_the_false_predicate_rule() {
    let source = indoc! {r#"
        module MAIN
          syntax K
          syntax KItem
          syntax KConfigVar [token]
          syntax Foo ::= "foo"
        endmodule
    "#};
    let definition = generate_sort_predicate_syntax(&parsed(source)).unwrap();
    let transformed = generate_sort_predicate_rules(&definition).unwrap();
    let rules = |predicate: &str| {
        transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
                Sentence::Rule {
                    body, attributes, ..
                } if Printer::new()
                    .print_term(body)
                    .starts_with(&format!("{predicate}(")) =>
                {
                    Some((
                        Printer::new().print_term(body),
                        attributes.get("owise").is_some(),
                    ))
                }
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        rules("isKConfigVar"),
        [(
            "isKConfigVar(K)=>#token(\"false\",\"Bool\")".to_owned(),
            true
        )]
    );
    // Control: a defined sort is below `KItem` by its role, so it is placeable at `K`.
    assert_eq!(
        rules("isFoo"),
        [
            ("isFoo(Foo)=>#token(\"true\",\"Bool\")".to_owned(), false),
            ("isFoo(K)=>#token(\"false\",\"Bool\")".to_owned(), true)
        ]
    );
}

#[test]
fn a_scaffolding_sort_declared_in_the_main_module_has_no_sort_predicate() {
    let source = indoc! {r#"
        module MAIN
          imports INT-SYNTAX
          syntax #Layout [token]
          syntax Foo ::= "foo"
        endmodule
    "#};
    let prelude = embedded("prelude.md").unwrap();
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("layout.k", source),
        "MAIN",
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
    let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let rules = compiled
        .execution_definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule {
                body, attributes, ..
            } if Printer::new().print_term(body).starts_with("`is#Layout`(") => Some((
                Printer::new().print_term(body),
                attributes.get("owise").is_some(),
            )),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(rules.is_empty(), "{rules:?}");
    assert!(!compiled.definition_kore.contains("Lblis'Hash'Layout"));
    assert!(!compiled.definition_kore.contains("inj{Sort'Hash'Layout"));
    assert!(
        compiled
            .definition_kore
            .contains("symbol LblisFoo{}(SortK{}) : SortBool{}")
    );
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let definition = concretize_cells(&definition).unwrap();
    let definition = add_cool_like_attributes(&definition);
    let rendered = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
                |sentence| matches!(&**sentence, Sentence::Rule { attributes, .. }
            if attributes.get("initializer").is_none()
                && attributes.get("cool-like").is_some())
            ),
        "{rendered:#?}"
    );
}

#[test]
fn marks_cool_like_rules_of_imported_modules_through_the_main_module() {
    // Every rule runs in the main module's configuration, which alone fixes the `maincell`, so
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
        .filter_map(|sentence| match &**sentence {
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
                           | "f(" Exp ")" [function, symbol(f)]
                           | "g(" Exp ")" [strict, symbol(g)]
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
            .find_map(|sentence| match &**sentence {
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
            catalog.production(catalog.lookup(&id).unwrap()),
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
        .filter_map(|sentence| match &**sentence {
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
        .filter(|sentence| matches!(&***sentence, Sentence::Context { .. }))
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

#[cfg(feature = "z3-inference")]
#[test]
fn unchanged_rules_keep_their_own_origins_after_context_alias_removal() {
    let source = "module MAIN\n  imports INT\n  syntax KResult ::= Int\n  syntax Exp ::= Int | foo(Exp) [strict(c)] | a() | b() | d()\n  context alias [c]: HERE\n  rule a() => 1\n  rule b() => 2\n  rule d() => 3\nendmodule\n";
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("main.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    let source_id = SourceId(
        loaded
            .source_table()
            .iter()
            .position(|candidate| candidate.logical == "main.k")
            .expect("the input source is registered"),
    );
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let main = artifacts.execution_definition.main_module().unwrap();
    let production_start = source.find("foo(Exp) [strict(c)]").unwrap();
    let production_end = production_start + "foo(Exp) [strict(c)]".len();
    let mut authored = BTreeSet::new();
    let mut heat = 0;
    let mut cool = 0;
    for sentence in &main.local_sentences {
        let Sentence::Rule { .. } = &**sentence else {
            continue;
        };
        let attributes = sentence.attributes();
        if attributes.source() != Some("main.k") {
            continue;
        }
        let (expected, authored_rule) = if let Some(location) = attributes.location()
            && (6..=8).contains(&location.start_line)
        {
            let line = location.start_line;
            let marker = match line {
                6 => "rule a() => 1",
                7 => "rule b() => 2",
                8 => "rule d() => 3",
                _ => unreachable!(),
            };
            authored.insert(line);
            let start = source.find(marker).unwrap();
            (start..start + marker.len(), true)
        } else if attributes.has(k_rust::definition::AttributeKey::Heat) {
            heat += 1;
            (production_start..production_end, false)
        } else if attributes.has(k_rust::definition::AttributeKey::Cool) {
            cool += 1;
            (production_start..production_end, false)
        } else {
            continue;
        };
        if let Some(record) = attributes.origin_record() {
            assert!(!record.origins.is_empty());
            for origin in record.origins.links() {
                match origin {
                    ProvenanceLink::Source { span } => {
                        assert_eq!(span.source, source_id);
                        assert!(
                            expected.start <= span.start && span.end <= expected.end,
                            "rule at {:?} has origin {span:?} outside {expected:?}",
                            attributes.location()
                        );
                    }
                    ProvenanceLink::Sentence { unique_id } if authored_rule => {
                        assert_eq!(
                            Some(unique_id.as_str()),
                            attributes.string(k_rust::definition::AttributeKey::UniqueId),
                            "authored rule at {:?} links another sentence",
                            attributes.location()
                        );
                    }
                    _ => panic!("strictness rule has non-source origin {origin:?}"),
                }
            }
        } else if attributes.has(k_rust::definition::AttributeKey::Heat)
            || attributes.has(k_rust::definition::AttributeKey::Cool)
        {
            panic!("generated strictness rule has no origin receipt");
        }
    }
    assert_eq!(authored, BTreeSet::from([6, 7, 8]));
    assert_eq!((heat, cool), (1, 1));
}

#[cfg(feature = "z3-inference")]
fn load_main_with_prelude(source: &str) -> k_rust::outer::LoadedDefinition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    load_with_options(
        ResolvedSource::new("main.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..LoadOptions::default()
        },
    )
    .unwrap()
}

/// The compile address of the loaded MAIN sentence `select` picks.
#[cfg(feature = "z3-inference")]
fn main_address(
    loaded: &k_rust::outer::LoadedDefinition,
    select: impl Fn(&Sentence) -> bool,
) -> InputAddress {
    let main = loaded.definition().main_module().unwrap();
    let indices = main
        .local_sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| select(sentence))
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [index] = indices.as_slice() else {
        panic!("expected one loaded MAIN sentence, found {indices:?}");
    };
    InputAddress::new(InputSpace::Compile, "MAIN", u32::try_from(*index).unwrap())
}

#[cfg(feature = "z3-inference")]
fn at_line(sentence: &Sentence, line: u32) -> bool {
    matches!(sentence, Sentence::Rule { .. })
        && sentence.attributes().source() == Some("main.k")
        && sentence
            .attributes()
            .location()
            .is_some_and(|location| location.start_line == line)
}

#[cfg(feature = "z3-inference")]
#[test]
fn every_execution_sentence_names_only_the_input_sentences_it_derives_from() {
    let source = "module MAIN\n  imports INT\n  syntax KResult ::= Int\n  syntax Exp ::= Int | foo(Exp) [strict(c)] | a() | b() | d()\n  context alias [c]: HERE\n  rule a() => 1\n  rule b() => 2\n  rule d() => 3\nendmodule\n";
    let loaded = load_main_with_prelude(source);
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let main = artifacts.execution_definition.main_module().unwrap();

    // (a) Every authored rule carries exactly its own compile address, whatever the passes
    // before it removed or inserted.
    for line in 6..=8 {
        let expected = main_address(&loaded, |sentence| at_line(sentence, line));
        let rules = main
            .local_sentences
            .iter()
            .filter(|sentence| at_line(sentence, line))
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), 1, "line {line}");
        assert_eq!(
            rules[0].attributes().input_addresses(),
            std::slice::from_ref(&expected),
            "line {line}"
        );
        let id = rules[0]
            .attributes()
            .string(AttributeKey::UniqueId)
            .unwrap();
        let provenance = &artifacts.sentence_provenance[id];
        assert_eq!(provenance.input_addresses, std::slice::from_ref(&expected));
        assert_eq!(
            provenance.input_sentence_kinds[&expected],
            k_rust::provenance::InputSentenceKind::Rule
        );
        assert_eq!(provenance.generated_by, None);
    }

    // (b) Heating and cooling rules derive from the strict production and the alias its
    // strict(c) names, in that order.
    let production = main_address(&loaded, |sentence| {
        matches!(sentence, Sentence::Production { items, .. }
            if items.first() == Some(&ProductionItem::Terminal("foo".into())))
    });
    let alias = main_address(&loaded, |sentence| {
        matches!(sentence, Sentence::ContextAlias { .. })
    });
    let strictness = main
        .local_sentences
        .iter()
        .filter(|sentence| {
            matches!(&***sentence, Sentence::Rule { .. })
                && (sentence.attributes().has(AttributeKey::Heat)
                    || sentence.attributes().has(AttributeKey::Cool))
        })
        .collect::<Vec<_>>();
    assert_eq!(strictness.len(), 2);
    for rule in strictness {
        assert_eq!(
            rule.attributes().input_addresses(),
            [production.clone(), alias.clone()]
        );
        let id = rule.attributes().string(AttributeKey::UniqueId).unwrap();
        let provenance = &artifacts.sentence_provenance[id];
        assert_eq!(
            provenance.input_addresses,
            [production.clone(), alias.clone()]
        );
        assert_eq!(
            provenance.input_sentence_kinds[&production],
            k_rust::provenance::InputSentenceKind::Production
        );
        assert_eq!(
            provenance.input_sentence_kinds[&alias],
            k_rust::provenance::InputSentenceKind::ContextAlias
        );
        assert_eq!(provenance.generated_by, None);
    }

    // Soundness over the whole execution definition: every named address exists in the
    // compiled input, and a sentence with a source location names only sentences at that
    // location or the strictness declarations it instantiates.
    for module in &artifacts.execution_definition.modules {
        for sentence in &module.local_sentences {
            for address in sentence.attributes().input_addresses() {
                assert_eq!(address.input, InputSpace::Compile);
                let input = loaded
                    .definition()
                    .modules
                    .iter()
                    .find(|candidate| candidate.name == address.module)
                    .and_then(|module| module.local_sentences.get(address.index as usize))
                    .unwrap_or_else(|| panic!("{address:?} names no input sentence"));
                if matches!(&**sentence, Sentence::Rule { .. })
                    && !sentence.attributes().has(AttributeKey::Heat)
                    && !sentence.attributes().has(AttributeKey::Cool)
                    && let Some(location) = sentence.attributes().location()
                {
                    assert_eq!(
                        input.attributes().location(),
                        Some(location),
                        "rule at {location:?} names {address:?}"
                    );
                }
            }
        }
    }

    let sort_predicate = artifacts
        .execution_definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .find(|sentence| {
            matches!(***sentence, Sentence::Rule { .. })
                && sentence.attributes().input_addresses().is_empty()
                && sentence
                    .attributes()
                    .origin_record()
                    .is_some_and(|record| record.pass == GeneratingPass::GenerateSortPredicateRules)
        })
        .expect("compilation generates an unowned sort-predicate rule");
    let id = sort_predicate
        .attributes()
        .string(AttributeKey::UniqueId)
        .unwrap();
    let provenance = &artifacts.sentence_provenance[id];
    assert!(provenance.input_addresses.is_empty());
    assert!(provenance.input_sentence_kinds.is_empty());
    assert_eq!(
        provenance.generated_by,
        Some(GeneratingPass::GenerateSortPredicateRules)
    );
}

/// Review round 1: a compile address restored from KRUST-PROVENANCE into a rearranged definition
/// names its old position; compilation restamps it with the position in the definition it
/// compiles.
#[cfg(feature = "z3-inference")]
#[test]
fn restored_compile_addresses_are_restamped_for_the_definition_being_compiled() {
    let source = "module MAIN\n  imports INT\n  syntax Exp ::= Int | a() | b()\n  rule a() => 1\n  rule b() => 2\nendmodule\n";
    let loaded = load_main_with_prelude(source);
    let mut definition = with_compile_addresses(loaded.definition().clone());
    let main = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap();
    let position = |line| {
        main.local_sentences
            .iter()
            .position(|sentence| at_line(sentence, line))
            .unwrap()
    };
    let (first, second) = (position(4), position(5));
    main.local_sentences.swap(first, second);
    let encoded =
        k_rust::definition::json::to_provenance_string(&definition, loaded.source_table()).unwrap();
    let restored = k_rust::definition::json::from_provenance_str(&encoded).unwrap();
    let relinked = k_rust::outer::LoadedDefinition::from_loaded_parts(k_rust::outer::LoadedParts {
        files: loaded.files().to_vec(),
        source_table: restored.source_table,
        definition: restored.definition,
        diagnostics: loaded.diagnostics().to_vec(),
    })
    .unwrap();
    let stale = |line| {
        relinked
            .definition()
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| at_line(sentence, line))
            .unwrap()
            .attributes()
            .input_addresses()
            .to_vec()
    };
    // The premise: each restored carrier names the other rule's current position.
    assert_eq!(
        stale(4),
        [main_address(&relinked, |sentence| at_line(sentence, 5))]
    );

    let artifacts = compile_loaded_definition(&relinked, CompileOptions::default()).unwrap();
    let main = artifacts.execution_definition.main_module().unwrap();
    for line in [4, 5] {
        let rules = main
            .local_sentences
            .iter()
            .filter(|sentence| at_line(sentence, line))
            .collect::<Vec<_>>();
        assert_eq!(rules.len(), 1);
        assert_eq!(
            rules[0].attributes().input_addresses(),
            [main_address(&relinked, |sentence| at_line(sentence, line))],
            "line {line}"
        );
    }
}

#[cfg(feature = "z3-inference")]
#[test]
fn equal_content_rules_keep_their_own_addresses_under_one_unique_id() {
    // (c) Equal content at different positions is one backend transition identity with two
    // authors.
    let source = "module MAIN\n  imports INT\n  syntax Exp ::= Int | e()\n  rule e() => 5\n  rule e() => 5\nendmodule\n";
    let loaded = load_main_with_prelude(source);
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let main = artifacts.execution_definition.main_module().unwrap();
    let rules = [4, 5].map(|line| {
        let expected = main_address(&loaded, |sentence| at_line(sentence, line));
        let rules = main
            .local_sentences
            .iter()
            .filter(|sentence| at_line(sentence, line))
            .collect::<Vec<_>>();
        let [rule] = rules.as_slice() else {
            panic!("line {line}: {rules:?}");
        };
        assert_eq!(rule.attributes().input_addresses(), [expected]);
        rule.attributes()
            .string(AttributeKey::UniqueId)
            .unwrap()
            .to_owned()
    });
    assert_eq!(rules[0], rules[1]);
    let addresses = [4, 5].map(|line| main_address(&loaded, |sentence| at_line(sentence, line)));
    assert_eq!(
        artifacts.sentence_provenance[&rules[0]].input_addresses,
        addresses
    );
    assert_eq!(
        artifacts
            .execution_rewrite_order
            .iter()
            .filter(|id| **id == rules[0])
            .count(),
        1
    );
}

#[test]
fn emitted_sentence_provenance_matches_kore_ids_with_unimported_prelude_modules() {
    let source = "module MAIN\n  imports INT\n  syntax Exp ::= Int | e() | f() [macro]\n  rule e() => 5\n  rule f() => e()\nendmodule\n";
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("main.k", source),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
    let emitted_ids = [&artifacts.definition_kore, &artifacts.macros_kore]
        .into_iter()
        .flat_map(|kore| kore.split("UNIQUE'Unds'ID{}(\"").skip(1))
        .map(|rest| rest.split('"').next().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    assert!(!artifacts.macros_kore.trim().is_empty());
    let resolved = ResolvedDefinition::resolve(&artifacts.execution_definition).unwrap();
    let main = resolved.module_id("MAIN").unwrap();
    let mut import_closure = resolved
        .transitive_imports(main)
        .into_iter()
        .map(|id| resolved.module(id).name.as_str())
        .collect::<BTreeSet<_>>();
    import_closure.insert("MAIN");
    assert!(artifacts.execution_definition.modules.iter().any(|module| {
        !import_closure.contains(module.name.as_str())
            && module.local_sentences.iter().any(|sentence| {
                matches!(&**sentence, Sentence::Rule { .. })
                    && sentence
                        .attributes()
                        .string(k_rust::definition::AttributeKey::UniqueId)
                        .is_some_and(|id| !emitted_ids.contains(id))
            })
    }));
    assert_eq!(
        artifacts
            .sentence_provenance
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>(),
        emitted_ids
    );
}

#[cfg(feature = "z3-inference")]
#[test]
fn emitted_sentence_provenance_includes_proof_claims() {
    let source = indoc! {r#"
        module DEF
          syntax State ::= "a" [symbol(a)] | "b" [symbol(b)]
          configuration <k> $PGM:State </k>
          rule <k> a => b </k>
        endmodule
        module SPEC
          imports DEF
          claim [reach]: <k> a => b </k>
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("spec.k", source),
        "SPEC",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..LoadOptions::default()
        },
    )
    .unwrap();
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            check_mode: k_rust::definition::CheckMode::Proof {
                definition_module: "DEF".into(),
            },
            default_claims_to_all_path: true,
            ..CompileOptions::default()
        },
    )
    .unwrap();
    let emitted_ids = artifacts
        .definition_kore
        .split("UNIQUE'Unds'ID{}(\"")
        .skip(1)
        .map(|rest| rest.split('"').next().unwrap().to_owned())
        .collect::<BTreeSet<_>>();
    let claim_id = artifacts
        .execution_definition
        .modules
        .iter()
        .find(|module| module.name == "SPEC")
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| matches!(&***sentence, Sentence::Claim { .. }))
        .unwrap()
        .attributes()
        .string(AttributeKey::UniqueId)
        .unwrap();
    assert!(emitted_ids.contains(claim_id));
    assert_eq!(
        artifacts
            .sentence_provenance
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>(),
        emitted_ids
    );
}

fn compile_address(module: &str, index: u32) -> InputAddress {
    InputAddress::new(InputSpace::Compile, module, index)
}

/// Give every sentence of `definition` its compile address through the wire attribute, as a
/// definition restored from KRUST-PROVENANCE would carry it.
fn with_compile_addresses(mut definition: Definition) -> Definition {
    for module in &mut definition.modules {
        let name = module.name.clone();
        for (index, sentence) in module.local_sentences.iter_mut().enumerate() {
            k_rust::definition::sentence_mut(sentence)
                .attributes_mut()
                .insert(
                    INPUT_ADDRESSES_ATTRIBUTE,
                    json!([{"input": "compile", "module": name, "index": index}]),
                );
        }
    }
    definition
}

/// Review round 1: equal context aliases the resolution keeps once, within one module and across
/// imported modules, are both authors of the contexts they instantiate.
#[test]
fn equal_context_aliases_all_author_the_contexts_they_instantiate() {
    let alias = || Sentence::ContextAlias {
        body: Term::variable("HERE"),
        requires: truth(),
        attributes: attributes(&[("label", json!("c"))]),
    };
    let strict = Sentence::Production {
        label: Some(Label::new("foo")),
        parameters: Vec::new(),
        sort: Sort::new("Exp"),
        items: vec![ProductionItem::NonTerminal {
            sort: Sort::new("Exp"),
            name: None,
        }],
        attributes: attributes(&[("strict", json!("c"))]),
    };
    let imported = |name: &str| FlatImport {
        name: name.into(),
        public: true,
    };
    let local = with_compile_addresses(Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module("MAIN", vec![alias(), strict.clone(), alias()]),
        ],
        attributes: Attributes::default(),
    });
    let mut main = module("MAIN", vec![strict]);
    main.imports = vec![imported("A"), imported("B")];
    let across = with_compile_addresses(Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module("A", vec![alias()]),
            module("B", vec![alias()]),
            main,
        ],
        attributes: Attributes::default(),
    });
    for (definition, expected) in [
        (
            local,
            vec![
                compile_address("MAIN", 1),
                compile_address("MAIN", 0),
                compile_address("MAIN", 2),
            ],
        ),
        (
            across,
            vec![
                compile_address("MAIN", 0),
                compile_address("A", 0),
                compile_address("B", 0),
            ],
        ),
    ] {
        let transformed = resolve_strict(&definition).unwrap();
        let contexts = transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter(|sentence| matches!(&***sentence, Sentence::Context { .. }))
            .map(|sentence| sentence.attributes().input_addresses().to_vec())
            .collect::<Vec<_>>();
        assert_eq!(contexts, [expected]);
    }
}

/// Review round 1: equal field projections of two productions that differ only in their own
/// attributes are one projection derived from both.
#[test]
fn equal_field_projections_keep_every_production_as_author() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Pair ::= pair(left: Int, right: Int) [symbol(pair)]
          syntax Pair ::= pair(left: Int, right: Int) [symbol(pair), format(%1%2%3%4%5%6)]
        endmodule
    "#};
    let definition =
        with_compile_addresses(generate_sort_predicate_syntax(&parsed(source)).unwrap());
    let is_pair = |sentence: &Sentence| matches!(sentence, Sentence::Production { label: Some(label), .. } if label.name == "pair");
    let pairs = definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| is_pair(sentence))
        .map(|(index, _)| compile_address("MAIN", u32::try_from(index).unwrap()))
        .collect::<Vec<_>>();
    assert_eq!(pairs.len(), 2);
    let transformed = generate_sort_projections(&definition).unwrap();
    let projections = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| {
            !is_pair(sentence)
                && sentence
                    .attributes()
                    .input_addresses()
                    .iter()
                    .any(|address| pairs.contains(address))
        })
        .collect::<Vec<_>>();
    // A production and a rule for each of the two fields.
    assert_eq!(projections.len(), 4, "{projections:#?}");
    for projection in projections {
        assert_eq!(projection.attributes().input_addresses(), pairs.as_slice());
    }
}

/// Review round 1: a stream rule specialized to a user's stream cell derives from the builtin
/// template and the stream production; an unblocking rule also derives from the user's rule.
#[test]
fn specialized_stream_rules_name_the_template_and_the_stream_production() {
    let definition = with_compile_addresses(io_fixture("stdin"));
    let transformed = resolve_io(&definition).unwrap();
    let stream_production = compile_address("MAIN", 0);
    let consume = compile_address("MAIN", 2);
    let unblock = compile_address("STDIN-STREAM", 1);
    let stream_rule = compile_address("STDIN-STREAM", 2);
    let main = transformed.main_module().unwrap();
    let rule_inputs = |marker: &str| {
        main.local_sentences
            .iter()
            .filter_map(|sentence| match &**sentence {
                Sentence::Rule { body, .. } if Printer::new().print_term(body).contains(marker) => {
                    Some(sentence.attributes().input_addresses().to_vec())
                }
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        rule_inputs("builtinStep"),
        [vec![stream_rule, stream_production.clone()]]
    );
    assert_eq!(
        rule_inputs("#parseInput"),
        [vec![consume, unblock, stream_production]]
    );
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
    // The hybrid rules mention `isFoo`, which exists because `Foo` is a defined sort.
    let foo = Sentence::SyntaxSort {
        parameters: Vec::new(),
        sort: Sort::new("Foo"),
        attributes: Attributes::default(),
    };
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module("MAIN", vec![foo, alias, strict]),
        ],
        attributes: Attributes::default(),
    };

    let transformed = resolve_strict(&definition).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        !main
            .local_sentences
            .iter()
            .any(|sentence| matches!(&**sentence, Sentence::ContextAlias { .. }))
    );
    let contexts = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        matches!(&**sentence, Sentence::Rule { body, requires, .. }
            if Printer::new().print_term(body).starts_with("isFoo(step(")
                && Printer::new().print_term(requires).contains("isFoo(K0)")
                && Printer::new().print_term(requires).contains("isFoo(K1)"))
    }));
}

/// The rules a `hybrid(S)` attribute generates mention `isS`, so the attribute is rejected when
/// the module has no `isS`: `S` is undeclared, or `S` is a declared sort without K terms (a
/// numeral, a `#` sort). A defined sort is the control.
#[test]
fn rejects_a_hybrid_sort_without_a_sort_predicate() {
    let source = indoc! {r#"
        module BOOL
        endmodule
        module MAIN
          imports BOOL
          syntax 8
          syntax #Foo ::= "foo"
          syntax Val ::= "v"
          syntax Exp ::= Val
          syntax Exp ::= a(Exp) [strict, hybrid(8), symbol(a)]
                       | b(Exp) [strict, hybrid(#Foo), symbol(b)]
                       | c(Exp) [strict, hybrid(Undef), symbol(c)]
                       | d(Exp) [strict, hybrid(Val), symbol(d)]
        endmodule
    "#};
    let error = resolve_strict(&parsed(source)).unwrap_err();
    let messages = error
        .diagnostics
        .iter()
        .map(|diagnostic| {
            assert_eq!(
                diagnostic.code,
                k_rust::diagnostic::DiagnosticCode::InvalidStrictness
            );
            diagnostic.message.as_str()
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        messages,
        BTreeSet::from([
            "Definition is missing function is#Foo required by the hybrid attribute. Sort #Foo has no sort predicate because it has no K terms; name a sort of K terms instead or declare 'syntax Bool ::= is#Foo(K) [symbol(is#Foo), function]'",
            "Definition is missing function is8 required by the hybrid attribute. Sort 8 has no sort predicate because it has no K terms; name a sort of K terms instead or declare 'syntax Bool ::= is8(K) [symbol(is8), function]'",
            "Definition is missing function isUndef required by the hybrid attribute. Please either declare sort Undef or declare 'syntax Bool ::= isUndef(K) [symbol(isUndef), function]'",
        ])
    );
}

/// A sequential context requires `isR` of its alias's result sort `R` on the positions before
/// its own. When the alias names no result and the production names one, the context's `result`
/// attribute (which the heat/cool pass checks) is the production's, while the side condition
/// mentions `isKResult`, so strictness resolution checks that `isKResult` exists. With `KResult`
/// declared the definition is accepted.
#[test]
fn rejects_a_sequential_context_alias_whose_side_condition_predicate_is_missing() {
    for (declarations, error) in [
        (
            "",
            Some(
                "Definition is missing function isKResult required by sequential strictness. Please either declare sort KResult or declare 'syntax Bool ::= isKResult(K) [symbol(isKResult), function]'",
            ),
        ),
        ("  syntax KResult\n", None),
    ] {
        let source = format!(
            "module BOOL\nendmodule\nmodule MAIN\n  imports BOOL\n{declarations}  syntax Val ::= \"v\"\n  syntax Exp ::= Val | foo(Exp, Exp) [seqstrict(c), result(Val), symbol(foo)]\n  context alias [c]: HERE\nendmodule\n"
        );
        let resolved = resolve_strict(&parsed(&source));
        match error {
            Some(message) => {
                let error = resolved.unwrap_err();
                assert_eq!(error.diagnostics.len(), 1, "{:?}", error.diagnostics);
                assert_eq!(
                    error.diagnostics[0].code,
                    k_rust::diagnostic::DiagnosticCode::InvalidStrictness
                );
                assert_eq!(error.diagnostics[0].message, message);
            }
            None => {
                resolved.unwrap();
            }
        }
    }
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
fn strictness_on_a_production_with_sort_parameters_is_rejected() {
    for (parameter, label, nonterminals, strictness) in [
        (
            "W",
            "pick",
            vec![
                Sort::with_parameters("MInt", vec![Sort::new("W")]),
                Sort::new("Int"),
            ],
            attributes(&[("strict", json!("2"))]),
        ),
        (
            "S",
            "wrap",
            vec![Sort::new("S")],
            attributes(&[("strict", json!("")), ("seqstrict", json!(""))]),
        ),
        (
            "W",
            "tag",
            vec![Sort::new("Exp")],
            attributes(&[("strict", json!(""))]),
        ),
        (
            "W",
            "pick",
            vec![
                Sort::with_parameters("MInt", vec![Sort::new("W")]),
                Sort::new("Int"),
            ],
            attributes(&[("strict", json!("1")), ("hybrid", json!(""))]),
        ),
    ] {
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                module("BOOL", Vec::new()),
                module(
                    "MAIN",
                    vec![Sentence::Production {
                        label: Some(Label::with_parameters(label, vec![Sort::new(parameter)])),
                        parameters: vec![Sort::new(parameter)],
                        sort: Sort::new("Foo"),
                        items: nonterminals
                            .into_iter()
                            .map(|sort| ProductionItem::NonTerminal { sort, name: None })
                            .collect(),
                        attributes: strictness,
                    }],
                ),
            ],
            attributes: Attributes::default(),
        };

        let diagnostics = resolve_strict(&definition).unwrap_err().diagnostics;
        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(
            diagnostics[0].code,
            k_rust::diagnostic::DiagnosticCode::InvalidStrictness
        );
        assert_eq!(
            diagnostics[0].message,
            format!(
                "Strictness is not supported on a production with sort parameters {{{parameter}}}: its evaluation contexts would range over every instantiation of the parameters. Write a context for each instance instead."
            )
        );
    }
}

#[test]
fn strictness_rejects_function_and_macro_productions_at_the_production() {
    for (kind, strictness, reason) in [
        ("function", "strict", "evaluated by its equations"),
        ("function", "seqstrict", "evaluated by its equations"),
        ("function", "strict(2)", "evaluated by its equations"),
        ("macro", "strict", "expanded before rewriting"),
    ] {
        let source = format!(
            "module BOOL\nendmodule\nmodule MAIN\n  syntax Exp ::= \"a\" [symbol(a)]\n  syntax Exp ::= \"f(\" Exp \",\" Exp \")\" [{kind}, {strictness}, symbol(f)]\nendmodule\n"
        );
        let definition = parsed(&source);
        let production = definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| {
                matches!(&***sentence, Sentence::Production { label: Some(label), .. } if label.name == "f")
            })
            .unwrap();
        let diagnostics = resolve_strict(&definition).unwrap_err().diagnostics;
        assert_eq!(
            diagnostics.len(),
            1,
            "{kind}, {strictness}: {diagnostics:?}"
        );
        let diagnostic = &diagnostics[0];
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidStrictness
        );
        assert_eq!(diagnostic.source.as_deref(), Some("definition.k"));
        assert_eq!(diagnostic.location, production.attributes().location());
        assert_eq!(diagnostic.location.unwrap().start_line, 5);
        assert!(diagnostic.message.contains(reason), "{diagnostic:?}");
    }
}

#[test]
fn strictness_rejects_brackets_tokens_and_matching_logic_connectives() {
    for (label, kind, items, reason) in [
        (
            "group",
            "bracket",
            vec![
                ProductionItem::Terminal("(".into()),
                ProductionItem::NonTerminal {
                    sort: Sort::new("Exp"),
                    name: None,
                },
                ProductionItem::Terminal(")".into()),
            ],
            "every parser erases it",
        ),
        (
            "literal",
            "token",
            vec![ProductionItem::regex("[a-z]+")],
            "domain values",
        ),
        (
            "#And",
            "",
            vec![
                ProductionItem::NonTerminal {
                    sort: Sort::new("Exp"),
                    name: None,
                },
                ProductionItem::NonTerminal {
                    sort: Sort::new("Exp"),
                    name: None,
                },
            ],
            "matching-logic connective",
        ),
    ] {
        let mut production_attributes = attributes(&[
            ("strict", json!("")),
            (k_rust::definition::SOURCE_ATTRIBUTE, json!("strict-kind.k")),
            (k_rust::definition::LOCATION_ATTRIBUTE, json!([7, 3, 7, 40])),
        ]);
        if !kind.is_empty() {
            production_attributes.insert(kind, json!(""));
        }
        let definition = Definition {
            main_module: "MAIN".into(),
            modules: vec![
                module("BOOL", Vec::new()),
                module(
                    "MAIN",
                    vec![Sentence::Production {
                        label: Some(Label::new(label)),
                        parameters: Vec::new(),
                        sort: Sort::new("Exp"),
                        items,
                        attributes: production_attributes,
                    }],
                ),
            ],
            attributes: Attributes::default(),
        };
        let diagnostics = resolve_strict(&definition).unwrap_err().diagnostics;
        assert_eq!(diagnostics.len(), 1, "{label}: {diagnostics:?}");
        assert_eq!(
            diagnostics[0].code,
            k_rust::diagnostic::DiagnosticCode::InvalidStrictness
        );
        assert_eq!(diagnostics[0].source.as_deref(), Some("strict-kind.k"));
        assert_eq!(diagnostics[0].location.unwrap().start_line, 7);
        assert!(diagnostics[0].message.contains(reason), "{diagnostics:?}");
    }
}

#[test]
fn strictness_still_lowers_a_constructor_with_a_domain_value_argument() {
    let source = indoc! {r#"
        module BOOL
        endmodule
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax Foo ::= "f(" Int ")" [strict, symbol(f)]
        endmodule
    "#};
    let transformed = resolve_strict(&parsed(source)).unwrap();
    let contexts = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Context { body, .. } => Some(body),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(contexts.len(), 1);
    assert!(matches!(
        contexts[0].unannotated(),
        Term::Apply { label, .. } if label.name == "f"
    ));
    let lowered = resolve_contexts(&transformed).unwrap();
    assert_eq!(
        lowered
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter(|sentence| sentence.attributes().get("heat").is_some()
                || sentence.attributes().get("cool").is_some())
            .count(),
        2
    );
}

#[test]
fn strictness_still_lowers_an_algebraic_constructor() {
    let source = indoc! {r#"
        module BOOL
        endmodule
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | Exp "+" Exp [assoc, strict, symbol(_+_)]
        endmodule
    "#};
    let transformed = resolve_strict(&parsed(source)).unwrap();
    assert_eq!(
        transformed
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .filter(|sentence| matches!(&***sentence, Sentence::Context { .. }))
            .count(),
        2
    );
    let lowered = resolve_contexts(&transformed).unwrap();
    for attribute in ["heat", "cool"] {
        assert_eq!(
            lowered
                .main_module()
                .unwrap()
                .local_sentences
                .iter()
                .filter(|sentence| sentence.attributes().get(attribute).is_some())
                .count(),
            2
        );
    }
}

#[test]
fn strictness_still_lowers_productions_without_sort_parameters() {
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![
            module("BOOL", Vec::new()),
            module(
                "MAIN",
                vec![
                    Sentence::Production {
                        label: Some(Label::new("step")),
                        parameters: Vec::new(),
                        sort: Sort::new("Exp"),
                        items: vec![ProductionItem::NonTerminal {
                            sort: Sort::new("Exp"),
                            name: None,
                        }],
                        attributes: attributes(&[("strict", json!(""))]),
                    },
                    Sentence::Production {
                        label: Some(Label::with_parameters("wrap", vec![Sort::new("S")])),
                        parameters: vec![Sort::new("S")],
                        sort: Sort::new("Foo"),
                        items: vec![ProductionItem::NonTerminal {
                            sort: Sort::new("S"),
                            name: None,
                        }],
                        attributes: Attributes::default(),
                    },
                ],
            ),
        ],
        attributes: Attributes::default(),
    };

    let transformed = resolve_strict(&definition).unwrap();
    let contexts = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Context { body, .. } => Some(body),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(contexts.len(), 1);
    assert!(matches!(
        contexts[0].unannotated(),
        Term::Apply { label, .. } if label == &Label::new("step")
    ));
    assert!(!Printer::new().print_term(contexts[0]).contains("wrap"));
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
        .filter_map(|sentence| match &**sentence {
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

    let subsorts = semantic_cast_sentence_subsorts();
    let transformed = resolve_semantic_casts_in_sentence(&subsorts, sentence).unwrap();
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
                            production: Some(
                                ProductionIdentity::from_hex(&format!("{:032x}", 3)).unwrap(),
                            ),
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

    let subsorts = semantic_cast_sentence_subsorts();
    let transformed =
        resolve_semantic_casts_with_predicates_in_sentence(&subsorts, sentence).unwrap();
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
    assert_eq!(
        compound_metadata.production,
        Some(ProductionIdentity::from_hex(&format!("{:032x}", 3)).unwrap())
    );
    assert_eq!(
        compound_metadata.span,
        Some(TermSpan {
            source: SourceId(7),
            start: 11,
            end: 17,
        })
    );
}

fn predicate_labels(term: &Term) -> Vec<String> {
    let mut labels = Vec::new();
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term.unannotated()
            && label.name.starts_with("is")
        {
            labels.push(label.name.clone());
        }
    });
    labels.sort();
    labels
}

#[test]
fn semantic_cast_predicates_cover_only_sorts_with_a_predicate_and_bag() {
    let sentence = Sentence::Rule {
        body: application(
            "body",
            vec![
                application("#SemanticCastTo8", vec![Term::variable("X")]),
                application("#SemanticCastToBag", vec![Term::variable("R")]),
            ],
        ),
        requires: application(
            "existing",
            vec![application("#SemanticCastToFoo", vec![Term::variable("Y")])],
        ),
        ensures: application(
            "ensures",
            vec![application("#SemanticCastTo8", vec![Term::variable("X")])],
        ),
        attributes: Attributes::default(),
    };

    let subsorts = semantic_cast_sentence_subsorts();
    let transformed =
        resolve_semantic_casts_with_predicates_in_sentence(&subsorts, sentence).unwrap();
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
                    "X" => Some(Sort::new("8")),
                    "Y" => Some(Sort::new("Foo")),
                    "R" => Some(Sort::new("Bag")),
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
    assert_eq!(predicate_labels(predicates), ["isBag", "isFoo"]);
    assert_eq!(predicate_labels(&requires), ["isBag", "isFoo"]);
}

#[test]
fn semantic_cast_to_a_sort_without_a_predicate_keeps_the_requires_as_written() {
    let written = application("existing", vec![Term::variable("X")]);
    let sentence = Sentence::Rule {
        body: application(
            "body",
            vec![application("#SemanticCastTo8", vec![Term::variable("X")])],
        ),
        requires: written.clone(),
        ensures: application("ensures", Vec::new()),
        attributes: Attributes::default(),
    };

    let subsorts = semantic_cast_sentence_subsorts();
    let transformed =
        resolve_semantic_casts_with_predicates_in_sentence(&subsorts, sentence).unwrap();
    let Sentence::Rule { body, requires, .. } = transformed else {
        unreachable!()
    };

    let expected_requires = application(
        "existing",
        vec![Term::Variable {
            name: "X".into(),
            sort: Some(Sort::new("8")),
        }],
    );
    assert_eq!(requires, expected_requires);
    assert!(predicate_labels(&requires).is_empty(), "{requires}");
    let Term::Apply { arguments, .. } = body.unannotated() else {
        panic!("expected the body application: {body}")
    };
    assert!(matches!(
        arguments.as_slice(),
        [Term::Variable { name, sort: Some(sort) }] if name == "X" && *sort == Sort::new("8")
    ));
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
        let subsorts = semantic_cast_sentence_subsorts();
        let transformed =
            resolve_semantic_casts_with_predicates_in_sentence(&subsorts, sentence).unwrap();
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
fn concretize_cells_recurses_only_into_ml_result_sort_children() {
    fn ml_production(
        name: &str,
        parameters: Vec<Sort>,
        result: Sort,
        arguments: Vec<Sort>,
    ) -> Sentence {
        Sentence::Production {
            label: Some(Label::new(name)),
            parameters,
            sort: result,
            items: arguments
                .into_iter()
                .map(|sort| ProductionItem::NonTerminal { sort, name: None })
                .collect(),
            attributes: Attributes::default(),
        }
    }

    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> <k> 0 </k> </top>
          syntax K
          syntax Map
        endmodule
    "#};
    let definition = add_implicit_computation_cell(&parsed(source)).unwrap();
    let mut definition = resolve_fresh_constants(&definition, 0).unwrap();
    let formal_operand = Sort::new("S1");
    let formal_result = Sort::new("S2");
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .unwrap()
        .local_sentences
        .extend(
            [
                ml_production(
                    "#Or",
                    vec![formal_result.clone()],
                    formal_result.clone(),
                    vec![formal_result.clone(), formal_result.clone()],
                ),
                ml_production(
                    "#Top",
                    vec![formal_result.clone()],
                    formal_result.clone(),
                    Vec::new(),
                ),
                ml_production(
                    "#Equals",
                    vec![formal_operand.clone(), formal_result.clone()],
                    formal_result.clone(),
                    vec![formal_operand.clone(), formal_operand.clone()],
                ),
                ml_production(
                    "#Exists",
                    vec![formal_operand.clone(), formal_result.clone()],
                    formal_result.clone(),
                    vec![formal_operand.clone(), formal_result.clone()],
                ),
            ]
            .into_iter()
            .map(std::sync::Arc::new),
        );
    let resolved = ResolvedDefinition::resolve(&definition).unwrap();
    let root_sort = Sort::new("GeneratedTopCell");
    let operand_sort = Sort::new("Int");
    let or_span = TermSpan {
        source: SourceId(9),
        start: 12,
        end: 48,
    };
    let int = |token: &str| Term::Token {
        token: token.into(),
        sort: operand_sort.clone(),
    };
    let open_k = |body| {
        application(
            "<k>",
            vec![
                application("#noDots", Vec::new()),
                body,
                application("#noDots", Vec::new()),
            ],
        )
    };
    let cases = [
        (
            Term::Apply {
                label: Label::with_parameters("#Or", vec![root_sort.clone()]),
                arguments: vec![open_k(int("0")), open_k(int("1"))],
            }
            .with_metadata(TermMetadata {
                span: Some(or_span),
                ..TermMetadata::default()
            }),
            "#Or",
        ),
        (
            Term::Apply {
                label: Label::with_parameters("#Top", vec![root_sort.clone()]),
                arguments: Vec::new(),
            },
            "#Top",
        ),
        (
            Term::Apply {
                label: Label::with_parameters(
                    "#Equals",
                    vec![operand_sort.clone(), root_sort.clone()],
                ),
                arguments: vec![int("0"), int("1")],
            },
            "#Equals",
        ),
        (
            Term::Apply {
                label: Label::with_parameters("#Exists", vec![operand_sort.clone(), root_sort]),
                arguments: vec![
                    Term::Variable {
                        name: "X".into(),
                        sort: Some(operand_sort.clone()),
                    },
                    open_k(int("0")),
                ],
            },
            "#Exists",
        ),
    ];

    for (body, expected_label) in cases {
        let sentence = Sentence::Rule {
            body,
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        };
        let (sentence, _) = concretize_cells_in_sentence(&resolved, "MAIN", sentence).unwrap();
        let Sentence::Rule { body, .. } = sentence else {
            unreachable!()
        };
        let Term::Apply { label, arguments } = body.unannotated() else {
            panic!("expected {expected_label}, found {body}")
        };
        assert_eq!(label.name, expected_label, "{body}");
        if expected_label == "#Or" {
            assert_eq!(
                body.metadata().and_then(|metadata| metadata.span),
                Some(or_span)
            );
        }
        match expected_label {
            "#Or" => assert!(arguments.iter().all(|argument| matches!(
                argument.unannotated(),
                Term::Apply { label, .. } if label.name == "<generatedTop>"
            ))),
            "#Top" => assert!(arguments.is_empty()),
            "#Equals" => assert!(
                arguments
                    .iter()
                    .all(|argument| matches!(argument.unannotated(), Term::Token { .. }))
            ),
            "#Exists" => assert!(
                matches!(
                    arguments.first().map(Term::unannotated),
                    Some(Term::Variable { .. })
                ) && matches!(
                    arguments.get(1).map(Term::unannotated),
                    Some(Term::Apply { label, .. }) if label.name == "<generatedTop>"
                )
            ),
            _ => unreachable!(),
        }
    }
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
fn contexts_reject_function_and_macro_roots_at_the_context() {
    for (label, declaration, rule, reason) in [
        ("f", "function, ", "", "evaluated by its equations"),
        ("m", "macro, ", "", "expanded before rewriting"),
        (
            "m",
            "",
            "  rule m(X:Exp) => X:Exp [macro]\n",
            "expanded before rewriting",
        ),
    ] {
        let source = format!(
            "module MAIN\n  syntax Exp ::= \"a\" [symbol(a)]\n  syntax Exp ::= \"{label}(\" Exp \")\" [{declaration}symbol({label})]\n{rule}  context {label}(HOLE)\nendmodule\n"
        );
        let definition = parsed(&source);
        let context = definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find(|sentence| matches!(&***sentence, Sentence::Context { .. }))
            .unwrap();
        let diagnostics = resolve_contexts(&definition).unwrap_err().diagnostics;
        assert_eq!(diagnostics.len(), 1, "{source}: {diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(
            diagnostic.code,
            k_rust::diagnostic::DiagnosticCode::InvalidContext
        );
        assert_eq!(diagnostic.source.as_deref(), Some("definition.k"));
        assert_eq!(diagnostic.location, context.attributes().location());
        assert_eq!(
            diagnostic.location.unwrap().start_line,
            if rule.is_empty() { 4 } else { 5 }
        );
        assert!(
            diagnostic
                .message
                .contains(&format!("Cannot compile a context rooted at {label}:")),
            "{diagnostic:?}"
        );
        assert!(diagnostic.message.contains(reason), "{diagnostic:?}");
    }
}

#[test]
fn contexts_still_lower_a_constructor_root() {
    let source = indoc! {r#"
        module MAIN
          syntax Exp ::= "a" [symbol(a)]
                       | "g(" Exp ")" [symbol(g)]
          context g(HOLE)
        endmodule
    "#};
    let transformed = resolve_contexts(&parsed(source)).unwrap();
    let main = transformed.main_module().unwrap();
    assert!(
        !main
            .local_sentences
            .iter()
            .any(|sentence| matches!(&**sentence, Sentence::Context { .. }))
    );
    for attribute in ["heat", "cool"] {
        assert_eq!(
            main.local_sentences
                .iter()
                .filter(|sentence| sentence.attributes().get(attribute).is_some())
                .count(),
            1
        );
    }
}

#[test]
fn contexts_use_production_metadata_to_distinguish_function_and_constructor_roots() {
    for (syntax, is_function) in [("f", true), ("g", false)] {
        let source = indoc! {r#"
            module MAIN
              syntax Exp ::= "a" [symbol(a)]
                           | "g(" Exp ")" [symbol(shared)]
                           | "f(" Exp ")" [function, symbol(shared)]
              context ROOT(HOLE)
            endmodule
        "#}
        .replace("ROOT", syntax);
        let definition = parsed(&source);
        let resolved = ResolvedDefinition::resolve(&definition).unwrap();
        let catalog = resolved.production_catalog(resolved.main_module_id());
        assert_eq!(catalog.productions_for(&LabelHead::new("shared")).len(), 2);
        let body = definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                Sentence::Context { body, .. } => Some(body),
                _ => None,
            })
            .unwrap();
        let identity = body.metadata().unwrap().production.unwrap();
        let selected = catalog.production(catalog.lookup(&identity).unwrap());
        assert_eq!(selected.attributes().get("function").is_some(), is_function);

        let result = resolve_contexts(&definition);
        if is_function {
            let diagnostics = result.unwrap_err().diagnostics;
            assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
            assert_eq!(
                diagnostics[0].code,
                k_rust::diagnostic::DiagnosticCode::InvalidContext
            );
            assert_eq!(diagnostics[0].location.unwrap().start_line, 5);
        } else {
            let transformed = result.unwrap();
            let main = transformed.main_module().unwrap();
            assert!(
                !main
                    .local_sentences
                    .iter()
                    .any(|sentence| matches!(&**sentence, Sentence::Context { .. }))
            );
            for attribute in ["heat", "cool"] {
                assert_eq!(
                    main.local_sentences
                        .iter()
                        .filter(|sentence| sentence.attributes().get(attribute).is_some())
                        .count(),
                    1
                );
            }
        }
    }
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
            .any(|sentence| matches!(&**sentence, Sentence::Context { .. }))
    );
    let generated = main
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
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
        .filter(|(_, sentence)| match &***sentence {
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

            if let Sentence::Rule { body, .. } = &***sentence {
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
        .filter_map(|sentence| match &**sentence {
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
        .filter_map(|sentence| match &**sentence {
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let transformed = minimize_term_construction(&definition).unwrap();
    let body = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
        .find_map(|sentence| match &**sentence {
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
fn rejects_non_associative_units_at_the_production_location() {
    let unit_attributes = attributes(&[
        ("unit", json!(".Items")),
        ("org.kframework.attributes.Source", json!("unit.k")),
        ("org.kframework.attributes.Location", json!([4, 1, 4, 18])),
    ]);
    let definition = Definition {
        main_module: "MAIN".into(),
        modules: vec![module(
            "MAIN",
            vec![
                production("_Items_", "Items", unit_attributes),
                production(".Items", "Items", Attributes::default()),
                rule(
                    application("_Items_", vec![application(".Items", Vec::new())]),
                    Attributes::default(),
                ),
            ],
        )],
        attributes: Attributes::default(),
    };
    let error = remove_unit(&definition).unwrap_err();
    assert_eq!(error.diagnostics.len(), 1);
    assert_eq!(
        error.diagnostics[0].code,
        k_rust::diagnostic::DiagnosticCode::InvalidUnitAttribute
    );
    assert_eq!(
        error.diagnostics[0].message,
        "production for _Items_ has a unit attribute but is not associative"
    );
    assert_eq!(error.diagnostics[0].source.as_deref(), Some("unit.k"));
    assert_eq!(error.diagnostics[0].location.unwrap().start_line, 4);
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
    let body = match &*transformed.main_module().unwrap().local_sentences[2] {
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
    assert_eq!(origin.origins.links(), [ProvenanceLink::Source { span }]);
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
    assert!(matches!(&*preserved, Sentence::Rule { body: actual, .. } if *actual == body));
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
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
    let Sentence::Rule { body, .. } = &**smt_lemma else {
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
                    let Sentence::Rule { body, .. } = &**sentence else {
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
        let expected = source.production(source.lookup(&old_index).unwrap());
        assert_eq!(
            target.production(target.lookup(&new_index).unwrap()),
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
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = add_implicit_computation_cell(&definition).unwrap();
    let definition = resolve_fresh_constants(&definition, 0).unwrap();
    let transformed = concretize_cells(&definition).unwrap();
    let (body, requires) = transformed
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
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

/// The one diagnostic expanding the macros of `source` reports, as (line, message).
fn macro_expansion_error(source: &str) -> (u32, String) {
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let error = expand_macros(&definition).expect_err("expansion should be rejected");
    assert_eq!(error.diagnostics.len(), 1, "{:?}", error.diagnostics);
    let diagnostic = &error.diagnostics[0];
    let location = diagnostic
        .location
        .unwrap_or_else(|| panic!("the error should be located: {diagnostic:?}"));
    (location.start_line, diagnostic.message.clone())
}

/// B2 of the generated-input experiment: a `macro-rec` rule whose expansion leads back to the
/// application it rewrote never terminates; expansion reports it at the rule instead of
/// recursing until the native stack overflows. The cycle may pass through several rules, and
/// `alias-rec` rules are expanded alike.
#[test]
fn a_cyclic_macro_rec_expansion_is_a_located_error() {
    for (source, line) in [
        // The reproducer.
        (
            indoc! {r#"
                module MAIN
                  syntax Foo ::= "t" [macro-rec] | "a"
                  rule t => t
                  rule a => t
                endmodule
            "#},
            3,
        ),
        (
            indoc! {r#"
                module MAIN
                  syntax Foo ::= "a" [macro-rec] | "b" [macro-rec] | "c"
                  rule a => b
                  rule b => a
                  rule c => a
                endmodule
            "#},
            3,
        ),
        (
            indoc! {r#"
                module MAIN
                  syntax Foo ::= "t" [alias-rec] | "a"
                  rule t => t
                  rule a => t
                endmodule
            "#},
            3,
        ),
    ] {
        let (start_line, message) = macro_expansion_error(source);
        assert_eq!(start_line, line, "{source}: {message}");
        assert!(
            message.contains("does not terminate") && message.contains("leads back"),
            "{source}: {message}"
        );
    }
}

/// A `macro-rec` expansion that builds an ever deeper term, by nesting rewrites inside results
/// or by growing the subject at the root, ends at the depth bound with a located error.
#[test]
fn a_macro_rec_expansion_that_deepens_forever_is_a_located_error() {
    for source in [
        indoc! {r#"
            module MAIN
              syntax Foo ::= "t" [macro-rec] | s(Foo) | "c"
              rule t => s(t)
              rule c => t
            endmodule
        "#},
        indoc! {r#"
            module MAIN
              syntax Foo ::= f(Foo) [macro-rec] | s(Foo) | "z" | "c"
              rule f(X) => f(s(X))
              rule c => f(z)
            endmodule
        "#},
    ] {
        let (start_line, message) = macro_expansion_error(source);
        assert_eq!(start_line, 3, "{source}: {message}");
        assert!(message.contains("levels deep"), "{source}: {message}");
    }
}

/// A `macro-rec` expansion that terminates expands, however long its chains of root rewrites:
/// `d` doubles a numeral by nesting rewrites 256 deep, and `cnt` then counts the resulting
/// 513-deep numeral down by 512 rewrites at the root. The test thread's default stack is
/// smaller than the expansion would take without growing it.
#[test]
fn a_deep_terminating_macro_rec_expansion_expands() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= d(Foo) [macro-rec] | s(Foo) | "z" | "c" | cnt(Foo) [macro-rec] | "done"
          rule d(s(X)) => s(s(d(X)))
          rule d(z) => z
          rule cnt(s(X)) => cnt(X)
          rule cnt(z) => done
          rule c => cnt(d(d(d(d(d(d(d(d(d(s(z)))))))))))
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let definition = propagate_macro_attributes(&definition).unwrap();
    let expanded = expand_macros(&definition).expect("a terminating expansion should succeed");
    let rule = expanded
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .map(|sentence| sentence.as_ref())
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => match body.unannotated() {
                Term::Rewrite { left, right }
                    if matches!(left.unannotated(), Term::Apply { label, .. } if label.name.starts_with("c_")) =>
                {
                    Some(right.as_ref().clone())
                }
                _ => None,
            },
            _ => None,
        })
        .expect("the rule for c should remain");
    let Term::Apply { label, arguments } = rule.unannotated() else {
        panic!("c should expand to an application: {rule:?}");
    };
    assert!(label.name.starts_with("done"), "{rule:?}");
    assert!(arguments.is_empty());
}

/// A binding copied into the result of a rewrite is expanded again there when it holds a
/// macro application, under the rules applied above the result rather than those applied
/// inside the binding before. The non-recursive `f(X) => g(f(X))` applies once on the path
/// of each expansion of the element: with the subject `rev(cons(f(a), nil), nil)`, in its
/// copy into `rev(nil, cons(.., nil))`, and in the copy of that accumulator into the final
/// result. Only a copy holding no macro application, such as the `nil` copies here, is kept
/// as it was expanded. (A rule's right side may not keep a macro symbol, so the reversal is
/// expanded as a program.)
#[test]
fn a_macro_rec_result_expands_its_bindings_again_where_they_hold_macro_applications() {
    let source = indoc! {r#"
        module MAIN
          syntax Elem ::= "a" [symbol(a)] | f(Elem) [macro, symbol(f)] | g(Elem) [symbol(g)]
          syntax List ::= "nil" [symbol(nil)] | cons(Elem, List) [symbol(cons)]
                        | rev(List, List) [macro-rec, symbol(rev)]
          rule f(X) => g(f(X))
          rule rev(cons(X, L), A) => rev(L, cons(X, A))
          rule rev(nil, A) => A
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let nil = || application("nil", Vec::new());
    let program = application(
        "rev",
        vec![
            application(
                "cons",
                vec![application("f", vec![application("a", Vec::new())]), nil()],
            ),
            nil(),
        ],
    );
    let expanded = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(program),
        &Sort::new("List"),
    )
    .expect("the reversal should expand")
    .into_term();
    let element = ["g", "g", "g"].into_iter().fold(
        application("f", vec![application("a", Vec::new())]),
        |inner, label| application(label, vec![inner]),
    );
    assert_eq!(expanded, application("cons", vec![element, nil()]));
}

/// Standalone terms are expanded under the same bounds as sentences: a program that applies a
/// cyclic `macro-rec` macro is rejected rather than overflowing the stack.
#[test]
fn a_cyclic_macro_rec_expansion_of_a_program_is_an_error() {
    let source = indoc! {r#"
        module MAIN
          syntax Foo ::= "t" [macro-rec, symbol(t)]
          rule t => t
        endmodule
    "#};
    let definition = resolve_semantic_casts(&parsed(source)).unwrap();
    let error = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(application("t", Vec::new())),
        &Sort::new("Foo"),
    )
    .expect_err("a cyclic expansion should be rejected");
    assert!(error.contains("does not terminate"), "{error}");
}

/// The cycle is found as well where a parametric macro head makes expansion read each
/// application's instance from the typing of its sentence.
#[test]
fn a_cyclic_parametric_macro_rec_expansion_is_a_located_error() {
    let (start_line, message) = macro_expansion_error(indoc! {r#"
        module MAIN
          syntax {S} S ::= t(S) [macro-rec]
          syntax Foo ::= "c" | "e"
          rule t(X:Foo) => t(X)
          rule c => t(e)
        endmodule
    "#});
    assert_eq!(start_line, 4, "{message}");
    assert!(message.contains("leads back"), "{message}");
}

/// Cons lists over `Elem`, a non-recursive macro `m` and a recursive list reversal `rev`, with
/// the rule `c => wrap(nil)` whose right side the deep-input tests replace.
const DEEP_LIST_SOURCE: &str = indoc! {r#"
    module MAIN
      syntax Elem ::= "a" [symbol(a)] | "m" [macro, symbol(m)]
      syntax List ::= "nil" [symbol(nil)] | cons(Elem, List) [symbol(cons)]
                    | rev(List, List) [macro-rec, symbol(rev)]
      syntax Foo ::= "c" [symbol(c)] | wrap(List) [symbol(wrap)]
      rule m => a
      rule rev(cons(X, L), A) => rev(L, cons(X, A))
      rule rev(nil, A) => A
      rule c => wrap(nil)
    endmodule
"#};

/// The list `cons(a, cons(a, ... cons(last, nil)))` with `length` elements, built without
/// recursion.
fn deep_list(length: usize, last: &str) -> Term {
    let mut list = application("nil", Vec::new());
    for index in 0..length {
        let element = if index == 0 { last } else { "a" };
        list = application("cons", vec![application(element, Vec::new()), list]);
    }
    list
}

/// The elements of a cons list, read without recursion.
fn list_elements(mut list: &Term) -> Vec<String> {
    let mut elements = Vec::new();
    loop {
        let Term::Apply { label, arguments } = list.unannotated() else {
            panic!("not a list: {list:?}");
        };
        match (label.name.as_str(), arguments.as_slice()) {
            ("nil", []) => return elements,
            ("cons", [element, rest]) => {
                let Term::Apply { label, .. } = element.unannotated() else {
                    panic!("not an element: {element:?}");
                };
                elements.push(label.name.clone());
                list = rest;
            }
            _ => panic!("not a list: {list:?}"),
        }
    }
}

/// `DEEP_LIST_SOURCE` with macro attributes propagated and the right side of `c => wrap(nil)`
/// replaced by `wrap(right)`.
fn deep_list_definition(right: Term) -> Definition {
    let definition = resolve_semantic_casts(&parsed(DEEP_LIST_SOURCE)).unwrap();
    let mut definition = propagate_macro_attributes(&definition).unwrap();
    let mut right = Some(right);
    for sentence in definition
        .modules
        .iter_mut()
        .flat_map(|module| &mut module.local_sentences)
    {
        let Sentence::Rule {
            body,
            requires,
            ensures,
            attributes,
        } = sentence.as_ref()
        else {
            continue;
        };
        let Term::Rewrite { left, .. } = body.unannotated() else {
            continue;
        };
        if !matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "c") {
            continue;
        }
        *sentence = std::sync::Arc::new(Sentence::Rule {
            body: rewrite(
                left.as_ref().clone(),
                application("wrap", vec![right.take().unwrap()]),
            ),
            requires: requires.clone(),
            ensures: ensures.clone(),
            attributes: attributes.clone(),
        });
    }
    assert!(right.is_none(), "the rule for c should be replaced");
    definition
}

/// The list under `wrap` on the right side of the expanded rule for `c`.
fn expanded_wrapped_list(expanded: &Definition) -> Vec<String> {
    for sentence in expanded
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
    {
        let Sentence::Rule { body, .. } = sentence.as_ref() else {
            continue;
        };
        let Term::Rewrite { left, right } = body.unannotated() else {
            continue;
        };
        if !matches!(left.unannotated(), Term::Apply { label, .. } if label.name == "c") {
            continue;
        }
        let Term::Apply { label, arguments } = right.unannotated() else {
            panic!("c should expand to wrap(...)");
        };
        assert_eq!(label.name, "wrap");
        return list_elements(&arguments[0]);
    }
    panic!("the rule for c should remain")
}

/// Non-recursive macros are not subject to the divergence bounds: an ordinary macro applied at
/// the innermost position of a list 5000 deep, in a rule and in a program, expands on the test
/// thread's default stack.
#[test]
fn a_non_recursive_macro_expands_at_the_bottom_of_a_deep_term() {
    const LENGTH: usize = 5_000;
    let mut expected = vec!["a".to_owned(); LENGTH];
    let definition = deep_list_definition(deep_list(LENGTH, "m"));
    let expanded = expand_macros(&definition).expect("the deep rule should expand");
    assert_eq!(expanded_wrapped_list(&expanded), expected);

    let program = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(deep_list(LENGTH, "m")),
        &Sort::new("List"),
    )
    .expect("the deep program should expand")
    .into_term();
    assert_eq!(list_elements(&program), expected);
    expected.clear();
}

/// The depth `macro-rec` rewrites may add along a path of any input, however shallow: the
/// expansion pass's `MIN_RECURSIVE_GROWTH`, which is private to it. Its divergence diagnostic
/// states the bound, and `a_terminating_macro_rec_recursion_over_a_deep_input_expands` checks
/// that it is this one, so a change to the pass's bound fails that test instead of leaving its
/// input too shallow to exceed the bound.
const MIN_RECURSIVE_GROWTH: usize = 1_000;

/// A terminating `macro-rec` recursion over a deep input expands. Reversing a list of `LENGTH`
/// elements makes `LENGTH` recursive rewrites; once the accumulator is the deeper argument, each
/// rewrite adds a level, `LENGTH / 2` in all. That is more than the fixed growth allowance but
/// less than the depth of the input, so the expansion succeeds only because the allowance rises
/// to the input's depth.
#[test]
fn a_terminating_macro_rec_recursion_over_a_deep_input_expands() {
    // 50 levels of growth beyond the fixed allowance. The growth is exact, so any excess tells
    // the input-depth allowance from the fixed one, and 50 levels leave room for a change of a
    // few levels in how depth is counted. Recording the provenance of the expanded rule grows
    // with the input's size times its depth, so the input is no longer than that.
    const LENGTH: usize = 2 * MIN_RECURSIVE_GROWTH + 100;
    let (_, message) = macro_expansion_error(indoc! {r#"
        module MAIN
          syntax Foo ::= "t" [macro-rec] | s(Foo) | "c"
          rule t => s(t)
          rule c => t
        endmodule
    "#});
    assert!(
        message.contains(&format!("the larger of {MIN_RECURSIVE_GROWTH} and")),
        "the fixed growth allowance is no longer {MIN_RECURSIVE_GROWTH}; size LENGTH from the new one: {message}"
    );

    let input = || {
        application(
            "rev",
            vec![deep_list(LENGTH, "a"), application("nil", Vec::new())],
        )
    };
    let definition = deep_list_definition(input());
    let expanded = expand_macros(&definition).expect("the reversal should expand");
    assert_eq!(expanded_wrapped_list(&expanded).len(), LENGTH);

    let program = expand_macros_in_term(
        &definition,
        "MAIN",
        ParsedProgram::from_term(input()),
        &Sort::new("List"),
    )
    .expect("the reversal of a program should expand")
    .into_term();
    assert_eq!(list_elements(&program).len(), LENGTH);
}
