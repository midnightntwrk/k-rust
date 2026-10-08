use indoc::indoc;
use k_rust::definition::{
    Attributes, ConfigurationError, ProductionItem, Sentence, expand_configurations,
    expand_configurations_with_diagnostics,
};
use k_rust::diagnostic::DiagnosticCode;
use k_rust::inner::resolve_configuration_bubbles;
use k_rust::kast::{Term, TermParts, TermSpan};
use k_rust::outer::{ResolvedSource, load};
use k_rust::provenance::{
    DestinationAnchor, GeneratingPass, ORIGIN_ATTRIBUTE, ProvenanceLink, SourceId,
};

fn parsed(source: &str) -> k_rust::definition::Definition {
    let parsed = k_rust::outer::parse("configuration.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    resolve_configuration_bubbles(&lowered).unwrap()
}

fn cell_content_sort(definition: &k_rust::definition::Definition, cell: &str) -> String {
    definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if label.name == cell => items.iter().find_map(|item| match item {
                ProductionItem::NonTerminal { sort, .. } => Some(sort.to_string()),
                _ => None,
            }),
            _ => None,
        })
        .expect("generated cell production")
}

#[test]
fn schematic_configuration_content_uses_the_inferred_k_instance() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= wrap(S) [function]
          configuration <foo> wrap(0) </foo>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();
    // The parser instantiates S at K for this content; the cell's content sort must be K.
    assert_eq!(cell_content_sort(&expanded, "<foo>"), "K");
}

#[test]
fn explicitly_cast_schematic_configuration_content_keeps_its_int_instance() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= wrap(S) [function]
          configuration <foo> (wrap(0)):Int </foo>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();
    assert_eq!(cell_content_sort(&expanded, "<foo>"), "Int");
}

// A parametric-head instance (MInt{8}) is inferred only by z3 sort inference; portable inference refuses parametric sorts.
#[cfg(feature = "z3-inference")]
#[test]
fn schematic_configuration_content_keeps_its_parametric_head_instance() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax {W} MInt{W}
          syntax MInt{8}
          syntax {W} MInt{W} ::= wrap(MInt{W}) [function]
          configuration <foo> wrap($PGM:MInt{8}) </foo>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();
    assert_eq!(cell_content_sort(&expanded, "<foo>"), "MInt{8}");
}

#[test]
fn uncast_schematic_configuration_content_is_rejected_at_its_sentence() {
    let mut definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax {S} S ::= wrap(S) [function]
          configuration <foo> 0 </foo>
        endmodule
    "#});
    let expected_label = definition.modules[0]
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                parameters,
                sort,
                ..
            } if parameters.contains(sort) => Some(label.name.clone()),
            _ => None,
        })
        .expect("the schematic wrap production");
    let configuration = definition.modules[0]
        .local_sentences
        .iter_mut()
        .find(|sentence| matches!(&***sentence, Sentence::Configuration { .. }))
        .unwrap();
    let Sentence::Configuration {
        body,
        ensures,
        attributes,
    } = &**configuration
    else {
        unreachable!();
    };
    let expected_source = attributes.source().map(str::to_owned);
    let expected_location = attributes.location();
    let TermParts::Apply {
        label,
        mut arguments,
    } = body.clone().into_unannotated().into_parts()
    else {
        panic!("configuration cell");
    };
    // A JSON caller can supply an application without the parser's inferred cast.
    arguments[2] = Term::apply(&expected_label, vec![arguments[2].clone()]);
    *configuration = std::sync::Arc::new(Sentence::Configuration {
        body: Term::Apply { label, arguments },
        ensures: ensures.clone(),
        attributes: attributes.clone(),
    });

    let error = expand_configurations(&definition)
        .expect_err("an uninstantiated schematic result cannot become a cell content sort");
    let ConfigurationError::Invalid {
        module,
        source,
        location,
        message,
    } = error
    else {
        panic!("expected the located schematic-result error");
    };
    assert_eq!(module, "MAIN");
    assert!(expected_source.is_some());
    assert!(expected_location.is_some());
    assert_eq!(source, expected_source);
    assert_eq!(location, expected_location);
    assert!(
        message.contains(&format!("{expected_label:?}")),
        "{message}"
    );
    assert!(message.contains("sort parameters"), "{message}");
    assert!(message.contains('S'), "{message}");
    assert!(
        message.contains("cast it to the intended instance"),
        "{message}"
    );
}

#[test]
fn configuration_projection_preserves_its_parsed_result_sort() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Val
          configuration <k> $PGM:Val </k> <cell> {$PGM}:>K </cell>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();
    assert_eq!(cell_content_sort(&expanded, "<cell>"), "K");
    let mut has_projection = false;
    for sentence in &expanded.main_module().unwrap().local_sentences {
        if let Sentence::Rule { body, .. } = &**sentence {
            body.visit_preorder(&mut |term| {
                has_projection |= matches!(term.unannotated(), Term::Apply { label, arguments }
                    if label.name == "project:K" && arguments.len() == 1);
            });
        }
    }
    assert!(
        has_projection,
        "the initializer must retain the outer-cast projection"
    );
}

#[test]
fn configuration_leaf_uses_declared_projection_labels_before_generated_signatures() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Value ::= "custom" [symbol(project:K)]
          configuration <cell> custom </cell>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();
    assert_eq!(cell_content_sort(&expanded, "<cell>"), "Value");
}

#[test]
fn generated_configuration_projection_does_not_trust_stale_metadata() {
    let mut definition = parsed(indoc! {r#"
        module MAIN
          configuration <cell> {$PGM}:>K </cell>
        endmodule
    "#});
    let body = definition.modules[0]
        .local_sentences
        .iter_mut()
        .find_map(
            |sentence| match k_rust::definition::sentence_mut(sentence) {
                Sentence::Configuration { body, .. } => Some(body),
                _ => None,
            },
        )
        .unwrap();
    let TermParts::Apply {
        label,
        mut arguments,
    } = body.clone().into_unannotated().into_parts()
    else {
        panic!("configuration cell");
    };
    arguments[2] = arguments[2]
        .clone()
        .with_metadata(k_rust::kast::TermMetadata {
            production: Some(
                k_rust::kast::ProductionIdentity::from_hex(&format!("{:032x}", usize::MAX))
                    .unwrap(),
            ),
            ..Default::default()
        });
    *body = Term::Apply { label, arguments };
    let expanded = expand_configurations(&definition).unwrap();
    assert_eq!(cell_content_sort(&expanded, "<cell>"), "K");
}

#[test]
fn collection_cell_with_config_variable_warns_without_initial() {
    let definition = parsed(indoc! {r#"
        module MAIN
          configuration
            <top>
              <good multiplicity="*" type="Set" initial=""> $FOO </good>
              <bad multiplicity="*" type="Set"> $FOO </bad>
            </top>
        endmodule
    "#});
    let (_, diagnostics) = expand_configurations_with_diagnostics(&definition).unwrap();
    let warnings = diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == DiagnosticCode::CellCollectionVarWithoutInitial)
        .collect::<Vec<_>>();
    assert_eq!(warnings.len(), 1);
    assert_eq!(
        warnings[0].message,
        "Configuration variable found in declaration of collection cell <bad>. Implicitly, this causes the initial configuration to start with one <bad> element instead of zero. Add the `initial=\"\"` attribute to make that behavior explicit."
    );
}

fn attributes(attributes: &Attributes) -> String {
    attributes
        .entries()
        .iter()
        .filter(|(key, _)| {
            !matches!(
                key.as_str(),
                "org.kframework.attributes.Source"
                    | "org.kframework.attributes.SourceId"
                    | "org.krust.provenance.Origin"
                    | "org.krust.provenance.SentenceStartOffset"
                    | "org.krust.provenance.SentenceEndOffset"
                    | "org.kframework.attributes.Location"
                    | "contentStartLine"
                    | "contentStartColumn"
                    | "contentStartOffset"
            )
        })
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn sentence_summary(sentences: &[std::sync::Arc<Sentence>]) -> Vec<String> {
    sentences
        .iter()
        .map(|sentence| match &**sentence {
            Sentence::SyntaxSort {
                sort,
                attributes: att,
                ..
            } => format!("syntax {sort} [{}]", attributes(att)),
            Sentence::Production {
                label,
                sort,
                items,
                attributes: att,
                ..
            } => {
                let items = items
                    .iter()
                    .map(|item| match item {
                        ProductionItem::NonTerminal { sort, .. } => sort.to_string(),
                        ProductionItem::Terminal(value) => format!("{value:?}"),
                        ProductionItem::RegexTerminal { regex, .. } => format!("r{regex:?}"),
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!(
                    "production {sort} ::= {items} label={} [{}]",
                    label.as_ref().map_or("-", |label| label.name.as_str()),
                    attributes(att)
                )
            }
            Sentence::Rule {
                body,
                requires,
                ensures,
                attributes: att,
            } => format!(
                "rule {body} requires {requires} ensures {ensures} [{}]",
                attributes(att)
            ),
            sentence => format!("{sentence:?}"),
        })
        .collect()
}

macro_rules! assert_configuration_snapshot {
    ($source:expr, $value:expr) => {{
        let source = $source;
        let value = $value;
        insta::with_settings!({
            description => format!("K definition:\n\n{source}"),
            omit_expression => true,
            prepend_module_to_snapshot => true,
        }, {
            insta::assert_debug_snapshot!(value);
        });
    }};
}

#[test]
fn generates_cell_fragment_collection_and_initializer_families() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration
            <threads>
              <thread multiplicity="*">
                <k> $PGM:Int </k>
                <opt multiplicity="?"> 0 </opt>
              </thread>
            </threads>
          ensures false
        endmodule
    "#};
    let definition = parsed(source);
    let expanded = expand_configurations(&definition).unwrap();

    assert!(
        !expanded
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(&**sentence, Sentence::Configuration { .. }))
    );
    assert_configuration_snapshot!(
        source,
        sentence_summary(&expanded.main_module().unwrap().local_sentences)
    );
}

fn assert_initializer_totality(source: &str, expected: &[(&str, bool)]) {
    let expanded = expand_configurations(&parsed(source)).unwrap();
    for &(name, _) in expected {
        assert_expanded_initializer_totality(&expanded, &[(name, false)]);
    }
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let loaded = load(
        ResolvedSource::new("configuration.k", source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let compiled = k_rust::kompile::compile_loaded_definition(
        &loaded,
        k_rust::kompile::CompileOptions::default(),
    )
    .unwrap();
    assert_expanded_initializer_totality(&compiled.execution_definition, expected);
    for &(name, total) in expected {
        let label = k_rust::kompile::encode_kore_label(&k_rust::kast::Label::new(name));
        let declaration = compiled
            .definition_kore
            .lines()
            .find(|line| {
                line.trim_start()
                    .starts_with(&format!("symbol {}{{}}()", label.name))
            })
            .expect("compiled nullary initializer declaration");
        assert_eq!(declaration.contains("total{}()"), total, "{declaration}");
        assert_eq!(
            declaration.contains("functional{}()"),
            total,
            "{declaration}"
        );
    }
}

fn assert_expanded_initializer_totality(
    expanded: &k_rust::definition::Definition,
    expected: &[(&str, bool)],
) {
    for &(name, total) in expected {
        let attributes = expanded
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .find_map(|sentence| match &**sentence {
                Sentence::Production {
                    label: Some(label),
                    attributes,
                    ..
                } if label.name == name => Some(attributes),
                _ => None,
            })
            .expect("generated initializer production");
        assert!(attributes.get("function").is_some(), "{name} is a function");
        assert_eq!(attributes.get("total").is_some(), total, "{name} totality");
    }
}

#[test]
fn source_written_initializer_marker_cannot_mint_totality() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Int ::= "fake" [initializer, function, symbol(fake)]
              rule fake => 0
              configuration <n> 0 </n>
            endmodule
        "#},
        &[("fake", false), ("initNCell", true)],
    );
}

#[test]
fn nullary_initializer_defined_token_is_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              configuration <n> 0 </n>
            endmodule
        "#},
        &[("initNCell", true)],
    );
}

#[test]
fn nullary_initializer_defined_children_are_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Map ::= ".Map" [symbol(.Map)]
              configuration <a> <b> .Map </b> </a>
            endmodule
        "#},
        &[("initBCell", true), ("initACell", true)],
    );
}

#[test]
fn nullary_initializer_optional_and_collection_children_are_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              configuration <a>
                <b multiplicity="?" initial=""> 0 </b>
                <c multiplicity="*" type="Set"> 0 </c>
              </a>
            endmodule
        "#},
        &[
            ("initBCell", true),
            ("initCCell", true),
            ("initACell", true),
        ],
    );
}

#[test]
fn nullary_initializer_optional_partial_content_is_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Int ::= p(Int) [function, symbol(p)]
              configuration <a> <b multiplicity="?" initial=""> p(0) </b> </a>
            endmodule
        "#},
        &[("initBCell", false), ("initACell", false)],
    );
}

#[test]
fn nullary_initializer_partial_content_and_parent_are_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Int ::= p(Int) [function, symbol(p)]
              syntax Int ::= Int "/Int" Int [function]
              rule p(X) => X /Int 0
              configuration <top> <n> p(0) </n> </top>
            endmodule
        "#},
        &[("initNCell", false), ("initTopCell", false)],
    );
}

#[test]
fn nullary_initializer_unresolved_anywhere_rule_is_not_total() {
    assert_initializer_totality(
        indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          syntax N ::= p(Int) [symbol(p)] | mk(Int) [symbol(mk)]
          syntax Int ::= Int "/Int" Int [function]
          rule p(X) => mk(X /Int 0) [anywhere]
          configuration <n> p(0) </n>
        endmodule
    "#},
        &[("initNCell", false)],
    );
}

#[test]
fn nullary_initializer_anywhere_cell_and_parent_are_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax Int ::= p(Int) [function, symbol(p)]
              syntax Int ::= Int "/Int" Int [function]
              rule p(X) => X /Int 0
              rule <n> 0 </n> => <n> p(0) </n> [anywhere]
              configuration <top> <n> 0 </n> </top>
            endmodule
        "#},
        &[("initNCell", false), ("initTopCell", false)],
    );
}

#[test]
fn nullary_initializer_function_cell_and_parent_are_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              configuration <top> <n function=""> 0 </n> </top>
            endmodule
        "#},
        &[("initNCell", false), ("initTopCell", false)],
    );
}

#[test]
fn nullary_initializer_anywhere_optional_unit_is_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax NCell ::= bad() [function, symbol(bad)]
              rule .NCell => bad() [anywhere]
              configuration <top> <n multiplicity="?"> 0 </n> </top>
            endmodule
        "#},
        &[("initNCell", true), ("initTopCell", false)],
    );
}

#[test]
fn nullary_initializer_anywhere_collection_unit_is_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax NCellSet ::= bad() [function, symbol(bad)]
              rule .NCellSet => bad() [anywhere]
              configuration <top> <n multiplicity="*" type="Set"> 0 </n> </top>
            endmodule
        "#},
        &[("initNCell", true), ("initTopCell", false)],
    );
}

#[test]
fn hooked_collection_unit_loses_hook_evidence_under_any_equation() {
    for (equation, total) in [
        ("", true),
        ("rule .NCellSet => bad()", false),
        ("rule .NCellSet => bad() [simplification]", true),
    ] {
        let source = format!(
            r#"module MAIN
              syntax Int ::= r"[0-9]+" [token]
              syntax NCellSet ::= bad() [function, symbol(bad)]
              {equation}
              configuration <top> <n multiplicity="*" type="Set"> 0 </n> </top>
            endmodule"#,
        );
        assert_initializer_totality(&source, &[("initNCell", true), ("initTopCell", total)]);
    }
}

#[test]
fn nullary_initializer_nontrivial_ensures_is_not_total() {
    assert_initializer_totality(
        indoc! {r#"
            module MAIN
              syntax Int ::= r"[0-9]+" [token]
              configuration <n> 0 </n> ensures false
            endmodule
        "#},
        &[("initNCell", false)],
    );
}

fn assert_repeated_initializer_totality(
    syntax: &str,
    first: &str,
    second: &str,
    expected: &[(&str, bool)],
) {
    for (first, second) in [(first, second), (second, first)] {
        let source = format!(
            "module MAIN\n  syntax Int ::= r\"[0-9]+\" [token]\n  {syntax}\n  {first}\n  {second}\nendmodule\n"
        );
        assert_initializer_totality(&source, expected);
    }
}

#[test]
fn nullary_initializer_repeated_configuration_partial_rule_is_not_total() {
    assert_repeated_initializer_totality(
        "syntax Int ::= p(Int) [function, symbol(p)]",
        "configuration <top> <n> 0 </n> </top>",
        "configuration <top> <n> p(0) </n> </top>",
        &[("initNCell", false), ("initTopCell", false)],
    );
}

#[test]
fn nullary_initializer_repeated_configuration_ensures_is_not_total() {
    assert_repeated_initializer_totality(
        "",
        "configuration <n> 0 </n>",
        "configuration <n> 0 </n> ensures false",
        &[("initNCell", false)],
    );
}

#[test]
fn nullary_initializer_repeated_defined_rules_are_total() {
    assert_repeated_initializer_totality(
        "",
        "configuration <a> <n> 0 </n> </a>",
        "configuration <a> <n> 0 </n> </a>",
        &[("initNCell", true), ("initACell", true)],
    );
}

#[test]
fn preserves_type_attribute_on_non_collection_cells() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top> <x type="Map"> 0 </x> </top>
        endmodule
    "#};
    let definition = parsed(source);
    let expanded =
        expand_configurations(&definition).expect("type is allowed without multiplicity");
    let x = expanded
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                attributes,
                ..
            } if label.name == "<x>" => Some(attributes),
            _ => None,
        })
        .expect("the x cell production should be generated");
    assert_eq!(x.get_str("type"), Some("Map"));
}

#[test]
fn rejects_reserved_generated_cell_names_during_expansion() {
    for cell_name in ["generatedTop", "generatedCounter"] {
        let source = format!(
            "module MAIN\n  syntax Int ::= r\"[0-9]+\" [token]\n  configuration <{cell_name}> 0 </{cell_name}>\nendmodule\n"
        );
        let definition = parsed(&source);
        let error = expand_configurations(&definition).expect_err("reserved cell names must fail");
        assert_eq!(
            error.to_string(),
            format!(
                "invalid configuration in module \"MAIN\": Cell name <{cell_name}> is reserved by K."
            )
        );
    }
}

#[test]
fn configuration_expansion_emits_origin_records() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> $PGM:Int </k>
        endmodule
    "#};
    let definition = parsed(source);
    let configuration_start = source.find("$PGM:Int").unwrap();
    let configuration_span = TermSpan {
        source: SourceId(0),
        start: configuration_start,
        end: configuration_start + "$PGM:Int".len(),
    };
    let expanded = expand_configurations(&definition).unwrap();
    let expanded_sentences = &expanded.main_module().unwrap().local_sentences;
    let initializers = expanded
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| sentence.attributes().get("initializer").is_some())
        .collect::<Vec<_>>();

    assert!(!initializers.is_empty());
    assert!(
        initializers.iter().all(|sentence| {
            sentence
                .attributes()
                .get(ORIGIN_ATTRIBUTE)
                .and_then(|origin| origin.get("pass"))
                .and_then(serde_json::Value::as_str)
                == Some("configuration-expansion")
        }),
        "every generated initializer sentence must name configuration expansion",
    );
    let (initializer_index, initializer) = expanded_sentences
        .iter()
        .enumerate()
        .find(|(_, sentence)| {
            matches!(&***sentence, Sentence::Rule { .. })
                && sentence.attributes().get("initializer").is_some()
        })
        .expect("configuration expansion emits an initializer rule");
    let sentence_anchor = format!("rule:{initializer_index}");
    let sentence_origin = initializer.attributes().get(ORIGIN_ATTRIBUTE).unwrap();
    assert_eq!(
        sentence_origin.get("destination"),
        Some(&serde_json::json!({
            "module": "MAIN",
            "sentence": sentence_anchor,
            "sentenceIndex": initializer_index,
            "path": [],
        })),
    );
    assert!(
        sentence_origin["origins"]
            .as_array()
            .unwrap()
            .contains(&serde_json::json!({
                "kind": "source",
                "source": configuration_span.source.0,
                "start": configuration_span.start,
                "end": configuration_span.end,
            })),
        "generated sentence links to the exact configuration source span: {sentence_origin}",
    );

    let Sentence::Rule { body, .. } = &**initializer else {
        unreachable!("initializer was selected as a rule");
    };
    let origin = body
        .metadata()
        .and_then(|metadata| metadata.origin.as_deref())
        .expect("generated initializer body has an origin");
    assert_eq!(origin.pass, GeneratingPass::ConfigurationExpansion);
    assert!(
        origin.origins.contains(&ProvenanceLink::Source {
            span: configuration_span,
        }),
        "generated term links to the exact configuration source span",
    );
    assert_eq!(
        origin.destination,
        Some(DestinationAnchor {
            module: "MAIN".into(),
            sentence: sentence_anchor.into(),
            sentence_index: u32::try_from(initializer_index).unwrap(),
            path: vec![0].into(),
        }),
    );
}

#[test]
fn generated_configuration_projections_discard_replaced_source_sort_metadata() {
    fn projection_metadata(term: &Term) -> Option<k_rust::kast::TermMetadata> {
        if matches!(term.unannotated(), Term::Apply { label, .. } if label.name == "project:Int") {
            return term.metadata().cloned();
        }
        match term.unannotated() {
            Term::Rewrite { left, right } => {
                projection_metadata(left).or_else(|| projection_metadata(right))
            }
            Term::As { pattern, alias } => {
                projection_metadata(pattern).or_else(|| projection_metadata(alias))
            }
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => {
                arguments.iter().find_map(projection_metadata)
            }
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
            Term::Annotated { .. } => unreachable!(),
        }
    }

    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <k> $PGM:Int </k>
        endmodule
    "#};
    let expanded = expand_configurations(&parsed(source)).unwrap();
    let rule_bodies = expanded
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        });
    let metadata = rule_bodies
        .filter_map(projection_metadata)
        .next()
        .expect("initializer should contain project:Int");
    assert_eq!(metadata.production, None);
    assert_eq!(metadata.sort, None);
}

#[test]
fn configuration_initializer_casts_are_lexically_scoped() {
    fn contains_token(term: &Term, expected: &str) -> bool {
        match term.unannotated() {
            Term::Token { token, .. } => token == expected,
            Term::Rewrite { left, right } => {
                contains_token(left, expected) || contains_token(right, expected)
            }
            Term::As { pattern, alias } => {
                contains_token(pattern, expected) || contains_token(alias, expected)
            }
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments
                .iter()
                .any(|argument| contains_token(argument, expected)),
            Term::InjectedLabel(_) | Term::Variable { .. } => false,
            Term::Annotated { .. } => unreachable!(),
        }
    }

    fn projection_for_token(term: &Term, expected: &str) -> Option<String> {
        match term.unannotated() {
            Term::Apply { label, arguments }
                if label.name.starts_with("project:")
                    && arguments
                        .iter()
                        .any(|argument| contains_token(argument, expected)) =>
            {
                Some(label.name.clone())
            }
            Term::Rewrite { left, right } => projection_for_token(left, expected)
                .or_else(|| projection_for_token(right, expected)),
            Term::As { pattern, alias } => projection_for_token(pattern, expected)
                .or_else(|| projection_for_token(alias, expected)),
            Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments
                .iter()
                .find_map(|argument| projection_for_token(argument, expected)),
            Term::InjectedLabel(_) | Term::Variable { .. } | Term::Token { .. } => None,
            Term::Annotated { .. } => unreachable!(),
        }
    }

    let source = indoc! {r#"
        module MAIN
          syntax Int
          configuration
            <top>
              <cast-first> $A:Int ~> #token("$B", "KConfigVar") </cast-first>
              <uncast-first> #token("$C", "KConfigVar") ~> $D:Int </uncast-first>
              <nested> ($E:Int ~> #token("$F", "KConfigVar")):K </nested>
              <k-cast> $G:K ~> #token("$H", "KConfigVar") </k-cast>
              <separate-cast> $I:Int </separate-cast>
              <separate-raw> #token("$J", "KConfigVar") </separate-raw>
              <literal> #token("1", "Int") </literal>
            </top>
        endmodule
    "#};
    let expanded = expand_configurations(&parsed(source)).unwrap();
    let rule_bodies = expanded
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter_map(|sentence| match &**sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .collect::<Vec<_>>();

    for token in ["$B", "$C", "$H", "$J"] {
        let projection = rule_bodies
            .iter()
            .find_map(|body| projection_for_token(body, token));
        assert_eq!(projection.as_deref(), Some("project:KItem"), "{token}");
    }
    for token in ["$F", "$G"] {
        assert_eq!(
            rule_bodies
                .iter()
                .find_map(|body| projection_for_token(body, token))
                .as_deref(),
            Some("project:K"),
            "{token}"
        );
    }
    assert!(
        rule_bodies.iter().any(|body| contains_token(body, "1")),
        "a non-configuration #token must retain its declared token value"
    );
}

#[test]
fn generates_map_set_and_list_cell_collections() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top>
            <entries multiplicity="*" type="Map"><key> 0 </key></entries>
            <workers multiplicity="*" type="Set"><worker> 0 </worker></workers>
            <queue multiplicity="*" type="List"><item> 0 </item></queue>
          </top>
        endmodule
    "#};
    let definition = parsed(source);
    let expanded = expand_configurations(&definition).unwrap();

    assert_configuration_snapshot!(
        source,
        sentence_summary(&expanded.main_module().unwrap().local_sentences)
    );
}

#[test]
fn wraps_multiple_top_level_cells_in_generated_top() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <left> 0 </left> <right> 1 </right>
        endmodule
    "#};
    let definition = parsed(source);
    let expanded = expand_configurations(&definition).unwrap();

    assert!(
        expanded
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(
                &**sentence,
                Sentence::Production { label: Some(label), .. }
                    if label.name == "<generatedTop>"
            ))
    );
    assert_configuration_snapshot!(
        source,
        sentence_summary(&expanded.main_module().unwrap().local_sentences)
    );
}

#[test]
fn configuration_parsing_always_includes_default_layout() {
    let source = indoc! {r#"
        module MAIN
          syntax #Layout [token]
          configuration
            <top>
              <k> .K </k>
            </top>
        endmodule
    "#};
    let definition = parsed(source);

    assert!(
        definition
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(&**sentence, Sentence::Configuration { .. }))
    );
}

#[test]
fn generates_stream_exit_and_builtin_cell_attributes() {
    let source = indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top>
            <out stream="stdout"> 0 </out>
            <status exit="" unused=""> 0 </status>
          </top>
        endmodule
    "#};
    let definition = parsed(source);
    let expanded = expand_configurations(&definition).unwrap();

    assert_configuration_snapshot!(
        source,
        sentence_summary(&expanded.main_module().unwrap().local_sentences)
    );
}

#[test]
fn resolves_external_cells_against_dependency_first_generated_initializers() {
    let base_source = indoc! {r#"
        module BASE
          syntax Int ::= r"[0-9]+" [token]
          configuration <shared> 0 </shared>
        endmodule
    "#};
    let main_source = indoc! {r#"
        requires "base.k"
        module MAIN
          imports BASE
          configuration <top><shared/></top>
        endmodule
    "#};
    let mut resolver = |_: &str, required: &str| match required {
        "base.k" => Ok(ResolvedSource::new("base.k", base_source)),
        _ => Err("not found".to_owned()),
    };
    let loaded = load(
        ResolvedSource::new("main.k", main_source),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let modules = loaded
        .definition()
        .modules
        .iter()
        .map(|module| {
            (
                module.name.clone(),
                sentence_summary(&module.local_sentences),
            )
        })
        .collect::<Vec<_>>();
    insta::with_settings!({
        description => format!("base.k:\n\n{base_source}\n\nmain.k:\n\n{main_source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(modules);
    });
}

macro_rules! expansion_error {
    ($name:ident, $configuration:literal) => {
        #[test]
        fn $name() {
            let source = concat!(
                "module MAIN\nsyntax Int ::= r\"[0-9]+\" [token]\nconfiguration ",
                $configuration,
                "\nendmodule"
            );
            let definition = parsed(source);
            let error = expand_configurations(&definition).unwrap_err();
            insta::with_settings!({
                description => format!("K definition:\n\n{source}"),
                omit_expression => true,
                prepend_module_to_snapshot => true,
            }, {
                insta::assert_debug_snapshot!(error);
            });
        }
    };
}

expansion_error!(rejects_mismatched_cell_names, "<one> 0 </two>");
expansion_error!(
    rejects_invalid_multiplicity,
    "<k multiplicity=\"+\"> 0 </k>"
);
expansion_error!(rejects_unrecognized_properties, "<k mystery=\"x\"> 0 </k>");
expansion_error!(rejects_empty_required_property, "<k color=\"\"> 0 </k>");
expansion_error!(
    rejects_nonempty_forbidden_property,
    "<k exit=\"bad\"> 0 </k>"
);
expansion_error!(
    rejects_empty_map_cell,
    "<map multiplicity=\"*\" type=\"Map\"> .Bag </map>"
);
expansion_error!(rejects_missing_external_cell, "<missing/>");
expansion_error!(
    rejects_invalid_collection_type,
    "<k multiplicity=\"*\" type=\"Queue\"> 0 </k>"
);

#[test]
fn configuration_resolution_is_an_identity_for_definitions_without_bubbles() {
    let definition = k_rust::definition::Definition {
        main_module: "MISSING".into(),
        modules: vec![],
        attributes: Default::default(),
    };
    assert_eq!(
        resolve_configuration_bubbles(&definition).unwrap(),
        definition
    );
}

#[test]
fn configuration_values_have_one_partial_transport_module_and_declared_projections() {
    let definition = parsed(indoc! {r#"
        module BASE
          syntax Val ::= "a"
          configuration <base> $A:K </base>
        endmodule
        module MAIN
          imports BASE
          configuration <top> <k> $PGM:K </k> <value> $X:Val </value> </top>
        endmodule
    "#});
    let before = k_rust_kore::measure::snapshot();
    let expanded = expand_configurations(&definition).unwrap();
    let work = k_rust_kore::measure::snapshot().delta(&before);
    // Both readers' imports are structural prerequisites of one resolution; expanding
    // their generated sentences must retain the incremental dependency-first updates.
    assert_eq!(
        work.get(k_rust_kore::measure::Counter::KompileResolveCalls),
        1
    );
    assert_eq!(
        work.get(k_rust_kore::measure::Counter::KompileResolveUpdates),
        2
    );
    let transport = expanded
        .modules
        .iter()
        .filter(|module| module.name == "K-RUST-CONFIGURATION-VALUES")
        .collect::<Vec<_>>();
    assert_eq!(transport.len(), 1);
    let transport = transport[0];
    assert_eq!(transport.local_sentences.len(), 3);
    for sentence in &transport.local_sentences {
        assert_eq!(
            sentence.attributes().origin_record().unwrap().pass,
            GeneratingPass::ConfigurationExpansion
        );
    }
    for (label, result, argument, function) in [
        ("#KConfigValue", "KItem", "K", false),
        ("#unboxKConfigValue", "K", "KItem", true),
    ] {
        let production = transport.local_sentences.iter().find(|sentence| {
            matches!(&***sentence, Sentence::Production {label: Some(found), ..} if found.name == label)
        }).unwrap();
        let Sentence::Production {
            sort,
            items,
            attributes,
            ..
        } = &**production
        else {
            unreachable!()
        };
        assert_eq!(sort.name, result);
        assert_eq!(
            items
                .iter()
                .filter_map(|item| match item {
                    ProductionItem::NonTerminal { sort, .. } => Some(sort.name.as_str()),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            vec![argument]
        );
        assert_eq!(
            attributes.has(k_rust::definition::AttributeKey::Function),
            function
        );
        assert!(!attributes.has(k_rust::definition::AttributeKey::Total));
        assert!(!attributes.has(k_rust::definition::AttributeKey::Functional));
    }
    let Sentence::Rule { body, .. } = &*transport.local_sentences[2] else {
        panic!("decoder equation")
    };
    let payload = Term::Variable {
        name: "KS".into(),
        sort: Some(k_rust::kast::Sort::new("K")),
    };
    assert!(k_rust::definition::term_equivalent(
        body,
        &Term::Rewrite {
            left: Box::new(Term::apply(
                "#unboxKConfigValue",
                vec![Term::apply("#KConfigValue", vec![payload.clone()])]
            )),
            right: Box::new(payload)
        }
    ));
    for name in ["BASE", "MAIN"] {
        let module = expanded
            .modules
            .iter()
            .find(|module| module.name == name)
            .unwrap();
        assert_eq!(
            module
                .imports
                .iter()
                .filter(|import| import.name == transport.name)
                .count(),
            1
        );
    }
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&expanded).unwrap();
    let visible = resolved.sentences(resolved.main_module_id());
    for label in ["#KConfigValue", "#unboxKConfigValue"] {
        assert_eq!(visible.iter().filter(|sentence| matches!(**sentence, Sentence::Production {label: Some(found), ..} if found.name == label)).count(), 1);
    }
    assert_eq!(expand_configurations(&expanded).unwrap(), expanded);
}

#[test]
fn transport_names_cannot_be_declared_by_source_modules() {
    for source in [
        indoc! {r#"
            module K-RUST-CONFIGURATION-VALUES
              syntax KItem ::= #KConfigValue(K) [symbol(#KConfigValue)]
              syntax K ::= #unboxKConfigValue(KItem) [function, symbol(#unboxKConfigValue)]
              rule #unboxKConfigValue(#KConfigValue(KS:K)) => KS
            endmodule
            module MAIN
              configuration <k> $PGM:K </k>
            endmodule
        "#},
        indoc! {r#"
            module K-RUST-CONFIGURATION-VALUES
            endmodule
            module MAIN
              configuration <k> $PGM:K </k>
            endmodule
        "#},
        indoc! {r#"
            module MAIN
              syntax KItem ::= custom(K) [symbol(#KConfigValue)]
              configuration <k> $PGM:K </k>
            endmodule
        "#},
        indoc! {r#"
            module MAIN
              syntax K ::= custom(KItem) [function, symbol(#unboxKConfigValue)]
              configuration <k> $PGM:K </k>
            endmodule
        "#},
    ] {
        let error =
            expand_configurations(&parsed(source)).expect_err("reserved source declaration");
        assert!(
            error
                .to_string()
                .contains("reserved for configuration-value transport"),
            "{error}"
        );
    }
}

#[test]
fn later_configuration_expansion_reuses_the_generated_transport_module() {
    let mut expanded = expand_configurations(&parsed(indoc! {r#"
        module MAIN
          configuration <base> $PGM:K </base>
        endmodule
    "#}))
    .unwrap();
    expanded = k_rust::kompile::number_sentences(&expanded);
    expanded = k_rust::kompile::generate_sort_predicate_syntax(&expanded).unwrap();
    expanded = k_rust::kompile::generate_sort_projections(&expanded).unwrap();
    let later = parsed(indoc! {r#"
        module MAIN
          configuration <later> $X:K </later>
        endmodule
    "#});
    expanded.modules.push(k_rust::definition::FlatModule {
        name: "LATER".into(),
        imports: vec![k_rust::definition::FlatImport {
            name: "MAIN".into(),
            public: true,
        }],
        local_sentences: later.main_module().unwrap().local_sentences.clone(),
        attributes: Attributes::default(),
    });
    expanded.main_module = "LATER".into();
    let expanded = expand_configurations(&expanded).unwrap();
    assert_eq!(
        expanded
            .modules
            .iter()
            .filter(|module| module.name == "K-RUST-CONFIGURATION-VALUES")
            .count(),
        1
    );
    let resolved = k_rust::definition::ResolvedDefinition::resolve(&expanded).unwrap();
    let visible = resolved.sentences(resolved.main_module_id());
    for label in ["#KConfigValue", "#unboxKConfigValue"] {
        assert_eq!(visible.iter().filter(|sentence| matches!(**sentence, Sentence::Production { label: Some(found), .. } if found.name == label)).count(), 1);
    }
}

#[test]
fn fresh_cell_expansion_reuses_the_numbered_transport_with_generated_helpers() {
    let mut definition = expand_configurations(&parsed(indoc! {r#"
        module MAIN
          configuration <k> $PGM:K </k>
        endmodule
    "#}))
    .unwrap();
    definition = k_rust::kompile::number_sentences(&definition);
    definition = k_rust::kompile::generate_sort_predicate_syntax(&definition).unwrap();
    definition = k_rust::kompile::generate_sort_projections(&definition).unwrap();
    let expanded = k_rust::kompile::resolve_fresh_constants(&definition, 0).unwrap();
    assert_eq!(
        expanded
            .modules
            .iter()
            .filter(|module| module.name == "K-RUST-CONFIGURATION-VALUES")
            .count(),
        1
    );
}

#[test]
fn reused_transport_rejects_changed_declaration_attributes() {
    for attribute in [
        k_rust::definition::AttributeKey::Total,
        k_rust::definition::AttributeKey::Functional,
        k_rust::definition::AttributeKey::Hook,
    ] {
        let mut expanded = expand_configurations(&parsed(indoc! {r#"
            module MAIN
              configuration <k> $PGM:K </k>
            endmodule
        "#}))
        .unwrap();
        let transport = expanded
            .modules
            .iter_mut()
            .find(|module| module.name == "K-RUST-CONFIGURATION-VALUES")
            .unwrap();
        k_rust::definition::sentence_mut(&mut transport.local_sentences[1])
            .attributes_mut()
            .insert(attribute.as_str(), serde_json::Value::String(String::new()));
        let error = expand_configurations(&expanded).expect_err("changed decoder semantics");
        assert!(
            error
                .to_string()
                .contains("reserved for configuration-value transport"),
            "{error}"
        );
    }
}

#[test]
fn nullary_initializers_do_not_generate_configuration_value_transport() {
    let expanded = expand_configurations(&parsed(indoc! {r#"
        module MAIN
          configuration <k> .K </k>
        endmodule
    "#}))
    .unwrap();
    assert!(
        !expanded
            .modules
            .iter()
            .any(|module| module.name == "K-RUST-CONFIGURATION-VALUES")
    );
}
