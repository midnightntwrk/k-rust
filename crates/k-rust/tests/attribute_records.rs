//! The keys `AttributeKey::is_source_position` and `AttributeKey::is_provenance_only` classify
//! are the only ones that move when text before a sentence moves: a definition and the same
//! definition with a blank line inserted load to sentences whose attributes differ, and are
//! equal once those keys are removed.

use std::collections::BTreeMap;

use k_rust::builtin::embedded;
use k_rust::definition::{AttributeKey, Definition, KeyRecord};
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::outer::{LoadOptions, ResolvedSource, load, load_with_options};
use serde_json::Value;

const DEFINITION: &str = r#"module SHIFT
  syntax S ::= "a" [symbol(a)] | "b" [symbol(b)]
  syntax S ::= f(S) [function, symbol(f)]
  rule f(a) => b
  rule [named]: f(b) => a
endmodule
"#;

/// The attribute maps of the main module's sentences, in order, each with or without the keys
/// that record positions or provenance.
fn sentence_attributes(source: &str, without_records: bool) -> Vec<BTreeMap<String, Value>> {
    let mut resolver = |_: &str, required: &str| Err(format!("unexpected require {required}"));
    let loaded = load(
        ResolvedSource::new("shift.k", source),
        "SHIFT",
        &mut resolver,
    )
    .unwrap();
    loaded
        .definition()
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .map(|sentence| {
            let mut entries = sentence.attributes().entries();
            if without_records {
                entries.retain(|key, _| {
                    !AttributeKey::from_name(key)
                        .is_some_and(|key| key.is_source_position() || key.is_provenance_only())
                });
            }
            entries
        })
        .collect()
}

#[test]
fn a_blank_line_moves_only_source_position_and_provenance_keys() {
    let shifted = DEFINITION.replacen("  rule f(a)", "\n  rule f(a)", 1);
    assert_ne!(
        sentence_attributes(DEFINITION, false),
        sentence_attributes(&shifted, false),
        "the inserted line moves the positions of the rules after it"
    );
    assert_eq!(
        sentence_attributes(DEFINITION, true),
        sentence_attributes(&shifted, true)
    );
}

/// A definition with syntax, strictness, a macro, a function, labelled and unlabelled rules and
/// a context, so that compilation generates sentences and krust records their provenance.
const COMPILED: &str = r#"module PROBE-SYNTAX
  imports INT-SYNTAX
  imports ID-SYNTAX
  syntax Exp ::= Int | Id
               | Exp "+" Exp [left, strict, symbol(myPlus)]
               | "(" Exp ")" [bracket]
               | "twice" "(" Exp ")" [macro, symbol(myTwice)]
               > "if" "(" Exp ")" Exp "else" Exp [strict(1), symbol(myIte)]
  syntax Stmt ::= Id "=" Exp ";" [strict(2), symbol(myAssign)]
                | Stmt Stmt [left, symbol(mySeq)]
                | "skip" [symbol(mySkip)]
  syntax KResult ::= Int
endmodule

module PROBE
  imports PROBE-SYNTAX
  imports INT
  imports MAP
  configuration <T> <k> $PGM:Stmt </k> <env> .Map </env> </T>

  syntax Int ::= f(Int) [function, symbol(myF)]
  rule f(0) => 1
  rule f(_) => 2 [owise]
  rule twice(E) => E + E
  rule I1:Int + I2:Int => I1 +Int I2
  rule [lookup]: <k> X:Id => V ...</k> <env>... X |-> V ...</env>
  rule <k> X = I:Int ; => .K ...</k> <env> E => E [ X <- I ] </env>
  rule S1:Stmt S2:Stmt => S1 ~> S2
  rule skip => .K
  rule if (I:Int) A else _ => A requires I =/=Int 0
  rule if (0) _ else B => B
  context if (HOLE) _ else _ [result(Int)]
endmodule
"#;

/// The compiled execution definition of `source`.
fn compiled(source: &str) -> Definition {
    let mut resolver = |_: &str, required: &str| {
        embedded(required).ok_or_else(|| format!("unexpected require {required}"))
    };
    let loaded = load_with_options(
        ResolvedSource::new("probe.k", source),
        "PROBE",
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![embedded("prelude.md").unwrap()],
            ..CompilationBackend::Rust.load_options()
        },
    )
    .unwrap();
    compile_loaded_definition(&loaded, CompileOptions::default())
        .unwrap()
        .execution_definition
}

/// One row per module and per sentence: its module, the sentence without attributes, its
/// `Content` attributes, and its other attributes.
type Row = (
    String,
    String,
    BTreeMap<String, Value>,
    BTreeMap<String, Value>,
);

fn rows(definition: &Definition) -> Vec<Row> {
    let split = |entries: BTreeMap<String, Value>| {
        let (content, records): (BTreeMap<_, _>, BTreeMap<_, _>) =
            entries.into_iter().partition(|(key, _)| {
                AttributeKey::from_name(key).is_none_or(|key| key.record() == KeyRecord::Content)
            });
        (content, records)
    };
    let mut rows = Vec::new();
    for module in &definition.modules {
        let (content, records) = split(module.attributes.entries());
        rows.push((module.name.clone(), "<module>".into(), content, records));
        for sentence in &module.local_sentences {
            let mut body = (**sentence).clone();
            *body.attributes_mut() = Default::default();
            let (content, records) = split(sentence.attributes().entries());
            rows.push((module.name.clone(), format!("{body:?}"), content, records));
        }
    }
    rows
}

/// Moving text in a definition moves, in the compiled definition (every module, its attributes,
/// and the sentences compilation generates), only keys whose record is not `Content`.
#[test]
fn moved_text_changes_only_records_in_the_compiled_definition() {
    let shifted = COMPILED
        .replacen("module PROBE\n", "\n\n// moved\nmodule PROBE\n", 1)
        .replacen("  rule f(0)", "\n\n  rule f(0)", 1)
        .replacen("rule if (0) _ else B", "rule if (0)\n   _ else B", 1)
        .replacen("  context if", "\n  context if", 1);
    let base = rows(&compiled(COMPILED));
    let moved = rows(&compiled(&shifted));
    assert_eq!(base.len(), moved.len());
    let mut moved_records = 0;
    for (left, right) in base.iter().zip(&moved) {
        assert_eq!((&left.0, &left.1), (&right.0, &right.1));
        assert_eq!(left.2, right.2, "content attributes of {}", left.1);
        if left.3 != right.3 {
            moved_records += 1;
        }
    }
    assert!(moved_records > 0, "the moved text moves some positions");
}
