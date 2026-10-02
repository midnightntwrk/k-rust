//! A loaded definition carries parsed sentences with its load normalizations established.
//!
//! A [`Sentence::Bubble`] is the text of a sentence that only the inner parser gives a meaning.
//! The compile passes and KORE emission are defined on parsed sentences and skip a bubble, so a
//! bubble that reached compilation would vanish from the compiled definition while compilation
//! succeeded. Every constructor of `LoadedDefinition` therefore rejects one.
//! Likewise, productions must already name their synonym denotations, and cell-sort declarations
//! must come from configuration expansion rather than temporary lowering placeholders.

use std::sync::Arc;

use k_rust::{
    builtin::embedded,
    definition::{Definition, Sentence},
    kast::Term,
    kompile::{CompileOptions, compile_loaded_definition},
    outer::{
        LoadError, LoadOptions, LoadedDefinition, LoadedParts, ResolvedSource, load_structured,
        load_with_options,
    },
};

const SOURCE: &str = r#"module MAIN
imports BOOL
syntax Foo ::= "a" [symbol(a)] | "b" [symbol(b)] | "f" "(" Foo ")" [function, symbol(f)]
rule f(a) => b
configuration <k> $PGM:Foo </k>
endmodule
"#;

/// The equation of `f`, which only the rule `f(a) => b` contributes to the compiled definition.
const F_EQUATION: &str = "Lblf{}(X0:SortFoo{})";

fn options() -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![embedded("prelude.md").unwrap()],
        ..Default::default()
    }
}

fn load_source() -> LoadedDefinition {
    load_with_options(
        ResolvedSource::new("main.k", SOURCE),
        "MAIN",
        &mut |_: &str, required: &str| {
            embedded(required)
                .ok_or_else(|| format!("embedded builtin source {required:?} was not found"))
        },
        &options(),
    )
    .unwrap_or_else(|error| panic!("the source should load: {error}"))
}

fn mentions_f(term: &Term) -> bool {
    let mut found = false;
    term.visit_preorder(&mut |term| {
        if let Term::Apply { label, .. } = term {
            found |= label.name == "f";
        }
    });
    found
}

fn lowered(source_name: &str, text: &str) -> Definition {
    k_rust::outer::lower(&k_rust::outer::parse(source_name, text).unwrap(), "MAIN").unwrap()
}

fn main_module(definition: &mut Definition) -> &mut k_rust::definition::FlatModule {
    definition
        .modules
        .iter_mut()
        .find(|module| module.name == "MAIN")
        .expect("the definition has a MAIN module")
}

#[test]
fn with_definition_rejects_a_rule_replaced_by_its_bubble() {
    let loaded = load_source();
    let control = compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the loaded source should compile: {error:?}"));
    assert!(
        control.definition_kore.contains(F_EQUATION),
        "the control compiles the equation of f"
    );

    let mut edited = loaded.definition().clone();
    let main = main_module(&mut edited);
    let index = main
        .local_sentences
        .iter()
        .position(|sentence| matches!(&**sentence, Sentence::Rule { body, .. } if mentions_f(body)))
        .expect("MAIN has the authored rule of f");
    let attributes = main.local_sentences[index].attributes().clone();
    main.local_sentences[index] = Arc::new(Sentence::Bubble {
        sentence_type: "rule".into(),
        contents: "f(a) => b".into(),
        attributes,
    });

    let error = loaded.with_definition(edited).unwrap_err();
    assert!(
        matches!(
            &error,
            LoadError::UnparsedBubble { module, sentence, sentence_type, source, .. }
                if module == "MAIN"
                    && *sentence == index
                    && sentence_type == "rule"
                    && source.as_deref() == Some("main.k")
        ),
        "{error:?}"
    );
}

#[test]
fn from_loaded_parts_rejects_lowered_text() {
    let text = "module MAIN\nsyntax Foo ::= \"a\" [symbol(a)] | \"b\" [symbol(b)]\nrule a => b\nconfiguration <k> $PGM:Foo </k>\nendmodule\n";
    let from_parts = |definition| {
        LoadedDefinition::from_loaded_parts(LoadedParts {
            files: Vec::new(),
            source_table: Default::default(),
            definition,
            diagnostics: Vec::new(),
        })
    };

    let error = from_parts(lowered("lowered.k", text)).unwrap_err();
    assert!(
        matches!(
            &error,
            LoadError::UnparsedBubble { module, sentence_type, source, .. }
                if module == "MAIN"
                    && sentence_type == "rule"
                    && source.as_deref() == Some("lowered.k")
        ),
        "{error:?}"
    );

    let without_rule = text.replace("rule a => b\n", "");
    let error = from_parts(lowered("lowered.k", &without_rule)).unwrap_err();
    assert!(
        matches!(
            &error,
            LoadError::UnparsedBubble { module, sentence_type, source, .. }
                if module == "MAIN"
                    && sentence_type == "config"
                    && source.as_deref() == Some("lowered.k")
        ),
        "{error:?}"
    );
}

#[test]
fn loading_rejects_a_bubble_no_inner_grammar_parses() {
    let control = load_structured(lowered("main.k", SOURCE), &options())
        .unwrap_or_else(|error| panic!("the lowered source should load: {error}"));
    let artifacts = compile_loaded_definition(&control, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the lowered source should compile: {error:?}"));
    assert!(
        artifacts.definition_kore.contains(F_EQUATION),
        "the control compiles the equation of f"
    );

    let mut definition = lowered("main.k", SOURCE);
    let main = main_module(&mut definition);
    let index = main
        .local_sentences
        .iter()
        .position(|sentence| {
            matches!(&**sentence, Sentence::Bubble { sentence_type, .. } if sentence_type == "rule")
        })
        .expect("the lowered MAIN has a rule bubble");
    let Sentence::Bubble {
        contents,
        attributes,
        ..
    } = &*main.local_sentences[index]
    else {
        unreachable!("the sentence was found as a bubble");
    };
    main.local_sentences[index] = Arc::new(Sentence::Bubble {
        sentence_type: "rul".into(),
        contents: contents.clone(),
        attributes: attributes.clone(),
    });

    let error = load_structured(definition, &options()).unwrap_err();
    assert!(
        matches!(
            &error,
            LoadError::UnparsedBubble { module, sentence_type, .. }
                if module == "MAIN" && sentence_type == "rul"
        ),
        "{error:?}"
    );
    let message = error.to_string();
    assert!(message.starts_with("main.k:"), "{message}");
    assert!(
        message.contains("is an unparsed \"rul\" bubble"),
        "{message}"
    );
}

#[test]
fn a_text_load_holds_no_bubble() {
    let loaded = load_source();
    for module in &loaded.definition().modules {
        for sentence in &module.local_sentences {
            assert!(
                !matches!(&**sentence, Sentence::Bubble { .. }),
                "module {} holds a bubble: {sentence:?}",
                module.name
            );
        }
    }
}

fn load_text(text: &str, module: &str) -> Result<LoadedDefinition, LoadError> {
    load_with_options(
        ResolvedSource::new("synonyms.k", text),
        module,
        &mut |_: &str, required: &str| {
            embedded(required)
                .ok_or_else(|| format!("embedded builtin source {required:?} was not found"))
        },
        &options(),
    )
}

fn g_argument(definition: &Definition) -> &k_rust::kast::Sort {
    definition
        .modules
        .iter()
        .flat_map(|module| &module.local_sentences)
        .find_map(|sentence| match &**sentence {
            Sentence::Production {
                label: Some(label),
                items,
                ..
            } if label.name == "g" => items.iter().find_map(|item| match item {
                k_rust::definition::ProductionItem::NonTerminal { sort, .. } => Some(sort),
                _ => None,
            }),
            _ => None,
        })
        .expect("the source declares g with an argument")
}

#[test]
fn with_definition_rejects_a_production_over_a_sort_synonym() {
    use k_rust::{definition::ProductionItem, kast::Sort};
    let text = "module MAIN\nimports INT\nsyntax Num = Int\nsyntax Foo ::= \"a\" [symbol(a)] | g(Num) [symbol(g)]\nconfiguration <k> $PGM:Foo </k>\nendmodule\n";
    let loaded = load_text(text, "MAIN").unwrap();
    assert_eq!(g_argument(loaded.definition()), &Sort::new("Int"));
    assert!(loaded.with_definition(loaded.definition().clone()).is_ok());
    let mut edited = loaded.definition().clone();
    let main = main_module(&mut edited);
    let index = main.local_sentences.iter().position(|sentence|
        matches!(&**sentence, Sentence::Production { label: Some(label), .. } if label.name == "g")
    ).unwrap();
    let Sentence::Production { items, .. } = Arc::make_mut(&mut main.local_sentences[index]) else {
        unreachable!("g was found as a production");
    };
    let sort = items
        .iter_mut()
        .find_map(|item| match item {
            ProductionItem::NonTerminal { sort, .. } => Some(sort),
            _ => None,
        })
        .unwrap();
    *sort = Sort::new("Num");
    let result = loaded.with_definition(edited);
    let error = result.unwrap_err();
    assert!(
        matches!(&error,
            LoadError::UnappliedSortSynonym { module, sentence, synonym, sort, source, location }
            if module == "MAIN" && *sentence == index && **synonym == Sort::new("Num")
                && **sort == Sort::new("Int") && source.as_deref() == Some("synonyms.k")
                && location.is_some_and(|location| location.start_line == 4)
        ),
        "{error:?}"
    );
    let message = error.to_string();
    assert!(message.starts_with("synonyms.k:4:"), "{message}");
    assert!(message.contains("sort synonym Num of Int"), "{message}");
}

#[test]
fn from_loaded_parts_rejects_a_temporary_cell_sort_declaration() {
    use k_rust::kast::Sort;
    let text =
        "module MAIN\nsyntax Foo ::= \"a\" [symbol(a)] | foo(FooCell) [symbol(foo)]\nendmodule\n";
    let result = LoadedDefinition::from_loaded_parts(LoadedParts {
        files: Vec::new(),
        source_table: Default::default(),
        definition: lowered("temporary.k", text),
        diagnostics: Vec::new(),
    });
    let error = result.unwrap_err();
    assert!(
        matches!(&error,
            LoadError::TemporaryCellSort { module, sort, source, location, .. }
            if module == "MAIN" && **sort == Sort::new("FooCell")
                && source.is_none()
                && location.is_none()
        ),
        "{error:?}"
    );
    let message = error.to_string();
    assert!(
        message.contains("declares FooCell with the internal temporary-cell-sort-decl attribute"),
        "{message}"
    );
}

#[test]
fn a_production_over_a_chained_synonym_loads_with_its_denotation() {
    let text = "module CHAIN\nimports INT\nsyntax B = Int\nsyntax A = B\nsyntax Foo ::= \"a\" [symbol(a)] | g(A) [symbol(g)]\nendmodule\n";
    let loaded = load_text(text, "CHAIN").unwrap();
    assert_eq!(
        g_argument(loaded.definition()),
        &k_rust::kast::Sort::new("Int")
    );
}

#[test]
fn a_configuration_cast_through_a_single_synonym_still_loads() {
    let text = "module MAIN\nimports INT\nsyntax Num = Int\nsyntax Foo ::= \"a\" [symbol(a)] | g(Num) [symbol(g)]\nconfiguration <k> $PGM:Foo </k> <n> 0:Num </n>\nendmodule\n";
    assert!(load_text(text, "MAIN").is_ok());
}
