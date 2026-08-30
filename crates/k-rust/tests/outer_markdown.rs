use indoc::indoc;
use k_rust::definition::Sentence;
use k_rust::outer::{
    LoadOptions, ResolvedSource, extract_fenced_k_code, extract_fenced_k_code_with_map,
    load_with_options,
};

#[test]
fn extracts_selected_fences_with_source_positions_intact() {
    let source = indoc! {r#"
        prose before
         ```k
         requires "base.md"
         ```
        ```{skip}
        module IGNORED endmodule
        ```
        ```{k enabled}
        module MAIN
          imports BASE
        endmodule
        ```
    "#};
    let extracted = extract_fenced_k_code(source, "k&!skip").unwrap();

    insta::with_settings!({
        description => format!("Markdown source:\n\n{source}"),
        omit_expression => true,
        prepend_module_to_snapshot => true,
    }, {
        insta::assert_debug_snapshot!(extracted);
    });
}

#[test]
fn extracted_ranges_map_back_to_raw_markdown_bytes() {
    let source = "π prose\n```k\nmodule MAIN\n  rule café => value\nendmodule\n```\ntail";
    let extracted = extract_fenced_k_code_with_map(source, "k").unwrap();
    let semantic_start = extracted.text.find("café => value").unwrap();
    let semantic_end = semantic_start + "café => value".len();
    let raw_start = source.find("café => value").unwrap();
    let raw_end = raw_start + "café => value".len();

    assert_eq!(
        extracted.offset_map.raw_range(semantic_start..semantic_end),
        Some(raw_start..raw_end)
    );
    assert_eq!(
        &extracted.text[semantic_start..semantic_end],
        &source[raw_start..raw_end]
    );
}

#[test]
fn loaded_rule_spans_resolve_to_raw_markdown_bytes() {
    let source = indoc! {r#"
        Documentation before the definition.

        ```k
        module MAIN
          syntax State ::= "start" [symbol(start)]
                         | "value" [symbol(value)]
          rule start => value
        endmodule
        ```

        Documentation after the definition.
    "#};
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected {required}"));
    let loaded = load_with_options(
        ResolvedSource::new("main.md", source),
        "MAIN",
        &mut resolver,
        &LoadOptions::default(),
    )
    .unwrap();
    let body = loaded
        .definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find_map(|sentence| match sentence {
            Sentence::Rule { body, .. } => Some(body),
            _ => None,
        })
        .expect("the Markdown rule should be resolved");
    let span = body
        .metadata()
        .and_then(|metadata| metadata.span)
        .expect("the parsed rule body should retain its semantic span");
    let raw_range = loaded
        .source_table
        .raw_range(span)
        .expect("the semantic span should resolve against raw Markdown");
    let extracted = extract_fenced_k_code(source, "k").unwrap();

    assert_eq!(&source[raw_range], &extracted[span.start..span.end]);
    assert_eq!(&extracted[span.start..span.end], "start => value");
}

#[test]
fn selector_supports_java_boolean_syntax_and_tag_spellings() {
    let source = indoc! {r#"
        ```{.k a}
        selected-a
        ```
        ```{k b}
        selected-b
        ```
        ```other
        other
        ```
    "#};

    assert!(
        extract_fenced_k_code(source, "k&a")
            .unwrap()
            .contains("selected-a")
    );
    assert!(
        !extract_fenced_k_code(source, "k&a")
            .unwrap()
            .contains("selected-b")
    );
    let either = extract_fenced_k_code(source, "(a|b)&!other").unwrap();
    assert!(either.contains("selected-a"));
    assert!(either.contains("selected-b"));
    assert!(!either.contains("other"));
    assert!(
        extract_fenced_k_code(source, "*")
            .unwrap()
            .contains("other")
    );
}

#[test]
fn rejects_malformed_selectors_and_annotations() {
    assert!(extract_fenced_k_code("```k\nmodule M endmodule\n```", "k|").is_err());
    assert!(extract_fenced_k_code("```{k a\nmodule M endmodule\n```", "k").is_err());
    assert!(extract_fenced_k_code("```k a\nmodule M endmodule\n```", "k").is_err());
}

#[test]
fn loader_processes_markdown_requires_with_the_selected_tags() {
    let entry = indoc! {r#"
        Documentation.

        ```k
        requires "base.md"
        module MAIN
          imports BASE
        endmodule
        ```
    "#};
    let base = indoc! {r#"
        ```{k disabled}
        module WRONG endmodule
        ```

        ```{k enabled}
        module BASE
          syntax Value ::= "value" [symbol(value)]
        endmodule
        ```
    "#};
    let mut resolver = |_: &str, required: &str| match required {
        "base.md" => Ok(ResolvedSource::new("base.md", base)),
        _ => Err(format!("missing {required}")),
    };

    let loaded = load_with_options(
        ResolvedSource::new("main.md", entry),
        "MAIN",
        &mut resolver,
        &LoadOptions {
            markdown_selector: "k&enabled|k&!disabled".into(),
            ..LoadOptions::default()
        },
    )
    .unwrap();

    assert!(loaded.resolved.module_id("MAIN").is_some());
    assert!(loaded.resolved.module_id("BASE").is_some());
    assert!(loaded.resolved.module_id("WRONG").is_none());
}
