//! `CompiledKoreArtifacts::sentence_provenance` names, for every rule compilation generates from
//! a source sentence, that sentence's input address (docs/compiled-sentence-provenance.md,
//! "Generated rules").
//!
//! The equations of a `#let`, a `#fun` or a match (`:=K`) are generated with no label and no
//! `Source` or `Location` of their own; the map is how a report names them, through the rule they
//! were lifted from. A function rule with configuration context (`[[ .. ]]`) is lowered to a
//! function equation that keeps its sentence's address.

use std::collections::BTreeSet;

use k_rust::builtin::embedded;
use k_rust::definition::{AttributeKey, Sentence};
use k_rust::kast::Term;
use k_rust::kompile::{CompileOptions, CompiledKoreArtifacts, compile_loaded_definition};
use k_rust::outer::{LoadOptions, LoadedDefinition, ResolvedSource, load_with_options};
use k_rust::provenance::{InputAddress, InputSpace};

fn load(source: &str) -> LoadedDefinition {
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
    .unwrap_or_else(|error| panic!("the definition loads: {error}"))
}

fn compile(loaded: &LoadedDefinition) -> CompiledKoreArtifacts {
    compile_loaded_definition(loaded, CompileOptions::default())
        .unwrap_or_else(|error| panic!("the definition compiles: {error}"))
}

/// The compile address of the loaded MAIN rule labelled `MAIN.{label}`.
fn address(loaded: &LoadedDefinition, label: &str) -> InputAddress {
    let label = format!("MAIN.{label}");
    let main = loaded.definition().main_module().unwrap();
    let indices = main
        .local_sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| {
            sentence.attributes().string(AttributeKey::Label) == Some(label.as_str())
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    let [index] = indices.as_slice() else {
        panic!("one loaded sentence {label} expected, found {indices:?}");
    };
    InputAddress::new(InputSpace::Compile, "MAIN", u32::try_from(*index).unwrap())
}

/// The head label of the left side of a rule's top rewrite.
fn left_head(sentence: &Sentence) -> Option<&str> {
    let Sentence::Rule { body, .. } = sentence else {
        return None;
    };
    let Term::Rewrite { left, .. } = body.unannotated() else {
        return None;
    };
    match left.unannotated() {
        Term::Apply { label, .. } => Some(label.name.as_str()),
        _ => None,
    }
}

fn unique_id(sentence: &Sentence) -> &str {
    sentence
        .attributes()
        .string(AttributeKey::UniqueId)
        .expect("an emitted rule has a UNIQUE_ID")
}

/// The `UNIQUE_ID`s of the compiled MAIN rules whose left side is headed by a label `select`
/// accepts, each with whether it is an `owise` rule.
fn rules_headed(
    artifacts: &CompiledKoreArtifacts,
    select: impl Fn(&str) -> bool,
) -> Vec<(String, bool)> {
    artifacts
        .execution_definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .filter(|sentence| left_head(sentence).is_some_and(&select))
        .map(|sentence| {
            (
                unique_id(sentence).to_owned(),
                sentence.attributes().has(AttributeKey::Owise),
            )
        })
        .collect()
}

/// The emitted `UNIQUE_ID`s of `definition_kore`.
fn emitted(artifacts: &CompiledKoreArtifacts) -> BTreeSet<String> {
    artifacts
        .definition_kore
        .split("UNIQUE'Unds'ID{}(\"")
        .skip(1)
        .map(|rest| rest.split('"').next().unwrap().to_owned())
        .collect()
}

const LOCAL_FUNCTIONS: &str = "module MAIN
  imports INT
  imports BOOL
  syntax Exp ::= Int | go(Int) | wrap(Int) | check(Int)
  rule [let]: go(X) => wrap(#let Y = X +Int 1 #in Y *Int 2)
  rule [fun]: wrap(X) => go(#fun(0 => 1)(X))
  rule [match]: check(I) => wrap(1) requires 0 :=K I
endmodule
";

#[test]
fn generated_lambda_equations_name_their_sentence() {
    let loaded = load(LOCAL_FUNCTIONS);
    let artifacts = compile(&loaded);
    let emitted = emitted(&artifacts);
    let lambdas = rules_headed(&artifacts, |label| label.starts_with("#lambda"));
    // `#let` gives one equation, the non-covering `#fun` its equation and its `owise`
    // refutation, the match its positive and its `owise` negative equation.
    assert_eq!(lambdas.len(), 5, "{lambdas:?}");
    assert_eq!(lambdas.iter().filter(|(_, owise)| *owise).count(), 2);
    let sources = ["let", "fun", "match"].map(|label| address(&loaded, label));
    let mut named = BTreeSet::new();
    for (id, _) in &lambdas {
        assert!(emitted.contains(id), "{id} is emitted");
        let provenance = &artifacts.sentence_provenance[id];
        let [only] = provenance.input_addresses.as_slice() else {
            panic!(
                "{id}: one address expected, {:?}",
                provenance.input_addresses
            );
        };
        assert!(sources.contains(only), "{id}: {only:?}");
        assert_eq!(provenance.generated_by, None, "{id}");
        named.insert(only.clone());
    }
    // Each of the three rules is the source of some generated equation.
    assert_eq!(named, sources.into_iter().collect());
    // Generated equations carry no label and no source position of their own.
    for sentence in &artifacts
        .execution_definition
        .main_module()
        .unwrap()
        .local_sentences
    {
        if left_head(sentence).is_some_and(|label| label.starts_with("#lambda")) {
            let attributes = sentence.attributes();
            assert_eq!(attributes.string(AttributeKey::Label), None);
            assert_eq!(attributes.source(), None);
            assert_eq!(attributes.location(), None);
        }
    }
}

const WITH_CONFIG: &str = "module MAIN
  imports INT
  configuration <k> $PGM:K </k> <n> 0 </n>
  syntax Int ::= f(Int) [function, symbol(f)]
  rule [wc]: [[ f(I) => I +Int N ]] <n> N </n>
endmodule
";

#[test]
fn with_config_equations_name_their_sentence() {
    let loaded = load(WITH_CONFIG);
    let artifacts = compile(&loaded);
    let emitted = emitted(&artifacts);
    let equations = rules_headed(&artifacts, |label| label == "f");
    let [(id, _)] = equations.as_slice() else {
        panic!("one equation of f expected: {equations:?}");
    };
    assert!(emitted.contains(id));
    assert_eq!(
        artifacts.sentence_provenance[id].input_addresses,
        [address(&loaded, "wc")]
    );
}

/// The source-to-KORE direction is the inverse of the map: the emitted rules of a sentence are
/// the keys whose addresses contain its address.
#[test]
fn the_emitted_rules_of_a_sentence_are_the_keys_naming_it() {
    let loaded = load(LOCAL_FUNCTIONS);
    let artifacts = compile(&loaded);
    let fun = address(&loaded, "fun");
    let keys = artifacts
        .sentence_provenance
        .iter()
        .filter(|(_, provenance)| provenance.input_addresses.contains(&fun))
        .map(|(id, _)| id.clone())
        .collect::<BTreeSet<_>>();
    // The rule itself, its lambda's equation and the lambda's refutation.
    assert_eq!(keys.len(), 3, "{keys:?}");
    let rule = artifacts
        .execution_definition
        .main_module()
        .unwrap()
        .local_sentences
        .iter()
        .find(|sentence| sentence.attributes().string(AttributeKey::Label) == Some("MAIN.fun"))
        .map(|sentence| unique_id(sentence).to_owned())
        .expect("the compiled rule keeps its label");
    assert!(keys.contains(&rule));
    let lambdas = rules_headed(&artifacts, |label| label.starts_with("#lambda"))
        .into_iter()
        .map(|(id, _)| id)
        .collect::<BTreeSet<_>>();
    assert_eq!(keys.iter().filter(|id| lambdas.contains(*id)).count(), 2);
}
