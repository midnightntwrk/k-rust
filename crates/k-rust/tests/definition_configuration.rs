use indoc::indoc;
use k_rust::definition::{Attributes, ProductionItem, Sentence, expand_configurations};
use k_rust::inner::{ConfigError, resolve_configuration_bubbles};
use k_rust::outer::{ResolvedSource, load};

fn parsed(source: &str) -> k_rust::definition::Definition {
    let parsed = k_rust::outer::parse("configuration.k", source).unwrap();
    let lowered = k_rust::outer::lower(&parsed, "MAIN").unwrap();
    resolve_configuration_bubbles(&lowered).unwrap()
}

fn attributes(attributes: &Attributes) -> String {
    attributes
        .entries()
        .iter()
        .filter(|(key, _)| {
            !matches!(
                key.as_str(),
                "org.kframework.attributes.Source"
                    | "org.kframework.attributes.Location"
                    | "contentStartLine"
                    | "contentStartColumn"
            )
        })
        .map(|(key, value)| format!("{key}={value}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn sentence_summary(sentences: &[Sentence]) -> Vec<String> {
    sentences
        .iter()
        .map(|sentence| match sentence {
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

#[test]
fn generates_java_cell_fragment_collection_and_initializer_families() {
    let definition = parsed(indoc! {r#"
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
    "#});
    let expanded = expand_configurations(&definition).unwrap();

    assert!(
        !expanded
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(sentence, Sentence::Configuration { .. }))
    );
    insta::assert_debug_snapshot!(sentence_summary(
        &expanded.main_module().unwrap().local_sentences
    ));
}

#[test]
fn generates_map_set_and_list_cell_collections() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top>
            <entries multiplicity="*" type="Map"><key> 0 </key></entries>
            <workers multiplicity="*" type="Set"><worker> 0 </worker></workers>
            <queue multiplicity="*" type="List"><item> 0 </item></queue>
          </top>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();

    insta::assert_debug_snapshot!(sentence_summary(
        &expanded.main_module().unwrap().local_sentences
    ));
}

#[test]
fn wraps_multiple_top_level_cells_in_generated_top() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <left> 0 </left> <right> 1 </right>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();

    assert!(
        expanded
            .main_module()
            .unwrap()
            .local_sentences
            .iter()
            .any(|sentence| matches!(
                sentence,
                Sentence::Production { label: Some(label), .. }
                    if label.name == "<generatedTop>"
            ))
    );
    insta::assert_debug_snapshot!(sentence_summary(
        &expanded.main_module().unwrap().local_sentences
    ));
}

#[test]
fn generates_stream_exit_and_builtin_cell_attributes() {
    let definition = parsed(indoc! {r#"
        module MAIN
          syntax Int ::= r"[0-9]+" [token]
          configuration <top>
            <out stream="stdout"> 0 </out>
            <status exit="" unused=""> 0 </status>
          </top>
        endmodule
    "#});
    let expanded = expand_configurations(&definition).unwrap();

    insta::assert_debug_snapshot!(sentence_summary(
        &expanded.main_module().unwrap().local_sentences
    ));
}

#[test]
fn resolves_external_cells_against_dependency_first_generated_initializers() {
    let mut resolver = |_: &str, required: &str| match required {
        "base.k" => Ok(ResolvedSource::new(
            "base.k",
            indoc! {r#"
                module BASE
                  syntax Int ::= r"[0-9]+" [token]
                  configuration <shared> 0 </shared>
                endmodule
            "#},
        )),
        _ => Err("not found".to_owned()),
    };
    let loaded = load(
        ResolvedSource::new(
            "main.k",
            indoc! {r#"
                requires "base.k"
                module MAIN
                  imports BASE
                  configuration <top><shared/></top>
                endmodule
            "#},
        ),
        "MAIN",
        &mut resolver,
    )
    .unwrap();
    let modules = loaded
        .definition
        .modules
        .iter()
        .map(|module| {
            (
                module.name.clone(),
                sentence_summary(&module.local_sentences),
            )
        })
        .collect::<Vec<_>>();
    insta::assert_debug_snapshot!(modules);
}

macro_rules! expansion_error {
    ($name:ident, $configuration:literal) => {
        #[test]
        fn $name() {
            let definition = parsed(concat!(
                "module MAIN\nsyntax Int ::= r\"[0-9]+\" [token]\nconfiguration ",
                $configuration,
                "\nendmodule"
            ));
            insta::assert_debug_snapshot!(expand_configurations(&definition).unwrap_err());
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
expansion_error!(rejects_type_without_star, "<k type=\"Set\"> 0 </k>");
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
fn parse_errors_remain_distinct_from_expansion_errors() {
    let definition = k_rust::definition::Definition {
        main_module: "MISSING".into(),
        modules: vec![],
        attributes: Default::default(),
    };
    assert!(matches!(
        resolve_configuration_bubbles(&definition),
        Err(ConfigError::Definition(_))
    ));
}
