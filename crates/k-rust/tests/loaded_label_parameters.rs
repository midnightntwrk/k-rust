//! Label sort parameters on loaded rule-like sentences.
//!
//! K source text cannot write a label parameter, so a source-loaded rule, claim, context,
//! context alias or configuration carries none: sort injection solves every parametric label
//! from its arguments and position.

use k_rust::builtin;
use k_rust::definition::Attributes;
use k_rust::definition::{Definition, FlatModule, Sentence};
use k_rust::inner::parse_rule_content;
use k_rust::kast::{Label, Sort, Term};
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::outer::{
    LoadOptions, LoadedDefinition, ResolvedSource, load_for_compilation, load_structured,
};

/// A user parametric production (`wrap`), `ite` through `#if`, and `#Equals` in a
/// simplification rule: the parser instantiates each of them while it disambiguates.
const SOURCE: &str = r#"
requires "domains.md"

module PARAMS-SYNTAX
  imports DOMAINS-SYNTAX
endmodule

module PARAMS
  imports DOMAINS
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax Num ::= Nat
  syntax {S} Wrap ::= wrap(S) [symbol(wrap)]
  syntax Wrap ::= f(Nat) [function, symbol(f)]
  syntax Int ::= g(Int) [function, symbol(g)]
  syntax Int ::= h(Int) [function, symbol(h)]
  rule [wrapping]: f(X:Nat) => wrap(X)
  rule [choice]: g(X) => #if X >Int 0 #then X #else 0 -Int X #fi
  rule [eq]: h(X) => 0 requires X ==Int 0
  rule [simp]: {h(X) #Equals 0} => {X #Equals 0} [simplification]
endmodule
"#;

const USER_MODULES: [&str; 2] = ["PARAMS", "PARAMS-SYNTAX"];

const BACKENDS: [CompilationBackend; 2] = [CompilationBackend::Rust, CompilationBackend::Llvm];

fn options(backend: CompilationBackend) -> LoadOptions {
    LoadOptions {
        implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
        excluded_module_attributes: vec![backend.excluded_module_attribute().to_owned()],
        ..LoadOptions::default()
    }
}

fn load_source(backend: CompilationBackend) -> LoadedDefinition {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    load_for_compilation(
        ResolvedSource::new("params.k", SOURCE.to_owned()),
        "PARAMS",
        None,
        &mut resolver,
        &options(backend),
    )
    .unwrap_or_else(|error| panic!("{backend}: the source definition loads: {error}"))
    .0
}

fn compile(loaded: &LoadedDefinition, backend: CompilationBackend) -> [String; 3] {
    let artifacts = compile_loaded_definition(
        loaded,
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{backend}: the definition compiles: {error}"));
    [
        artifacts.definition_kore,
        artifacts.syntax_definition_kore,
        artifacts.macros_kore,
    ]
}

fn visit_labels(term: &mut Term, visit: &mut impl FnMut(&mut Label)) {
    match term {
        Term::Annotated { term, .. } => visit_labels(term, visit),
        Term::Rewrite { left, right } => {
            visit_labels(left, visit);
            visit_labels(right, visit);
        }
        Term::As { pattern, alias } => {
            visit_labels(pattern, visit);
            visit_labels(alias, visit);
        }
        Term::Sequence(items) => items.iter_mut().for_each(|item| visit_labels(item, visit)),
        Term::Apply { label, arguments } => {
            visit(label);
            arguments
                .iter_mut()
                .for_each(|argument| visit_labels(argument, visit));
        }
        Term::InjectedLabel(label) => visit(label),
        Term::Variable { .. } | Term::Token { .. } => {}
    }
}

fn rule_like_terms(sentence: &mut Sentence) -> Vec<&mut Term> {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        }
        | Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => vec![body, requires, ensures],
        Sentence::Context { body, requires, .. }
        | Sentence::ContextAlias { body, requires, .. } => vec![body, requires],
        Sentence::Configuration { body, ensures, .. } => vec![body, ensures],
        _ => Vec::new(),
    }
}

fn for_each_rule_like_label(module: &mut FlatModule, mut visit: impl FnMut(&mut Label)) {
    for sentence in &mut module.local_sentences {
        for term in rule_like_terms(k_rust::definition::sentence_mut(sentence)) {
            visit_labels(term, &mut visit);
        }
    }
}

/// Every label in every rule-like sentence of `definition`, as `name{parameters}`.
fn rule_like_labels(definition: &Definition) -> Vec<(String, Label)> {
    let mut definition = definition.clone();
    let mut labels = Vec::new();
    for module in &mut definition.modules {
        let name = module.name.clone();
        for_each_rule_like_label(module, |label| labels.push((name.clone(), label.clone())));
    }
    labels
}

#[test]
fn source_loaded_rule_like_sentences_carry_no_label_parameter() {
    for backend in BACKENDS {
        let loaded = load_source(backend);
        let labels = rule_like_labels(&loaded.definition);
        for name in ["wrap", "ite", "#Equals"] {
            assert!(
                labels
                    .iter()
                    .any(|(module, label)| module == "PARAMS" && label.name == name),
                "{backend}: PARAMS applies {name}"
            );
        }
        let parameterised = labels
            .iter()
            .filter(|(_, label)| !label.parameters.is_empty())
            .map(|(module, label)| format!("{module}: {label}"))
            .collect::<Vec<_>>();
        assert!(
            parameterised.is_empty(),
            "{backend}: loaded rule-like labels with parameters: {parameterised:?}"
        );
    }
}

/// One parametric production per sentence kind, each applied only in that kind: `box` in the
/// configuration, `cl` in a claim, `cx` in a context, `al` in a context alias's side condition,
/// and `wrap` in a rule. The parser instantiates each application.
const KINDS_SOURCE: &str = r#"
requires "domains.md"

module KINDS-SYNTAX
  imports DOMAINS-SYNTAX
endmodule

module KINDS
  imports DOMAINS
  syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
  syntax {S} Wrap ::= wrap(S) [symbol(wrap)]
  syntax {S} Box ::= box(S) [symbol(box)]
  syntax {S} Cl ::= cl(S) [symbol(cl)]
  syntax {S} KItem ::= cx(S) [symbol(cx)]
  syntax {S} Bool ::= al(S) [function, total, symbol(al)]
  syntax Wrap ::= f(Nat) [function, symbol(f)]
  configuration <k> $PGM:K </k> <b> box(z) </b>
  rule f(X:Nat) => wrap(X)
  claim cl(z) => cl(s(z))
  context cx(HOLE:Int)
  context alias [kinds]: <k> HERE:K ...</k> requires al(1)
endmodule
"#;

fn kind_of(sentence: &Sentence) -> &'static str {
    match sentence {
        Sentence::Rule { .. } => "rule",
        Sentence::Claim { .. } => "claim",
        Sentence::Context { .. } => "context",
        Sentence::ContextAlias { .. } => "context alias",
        Sentence::Configuration { .. } => "configuration",
        _ => "other",
    }
}

/// Every kind of loaded rule-like sentence, and a rule parsed with `parse_rule_content`, carries
/// its parametric application without a parameter. The configuration is loaded as the
/// initializer rules its expansion generates, which carry its body.
#[test]
fn every_rule_like_sentence_kind_loads_parametric_applications_without_parameters() {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let loaded = load_for_compilation(
        ResolvedSource::new("kinds.k", KINDS_SOURCE.to_owned()),
        "KINDS",
        None,
        &mut resolver,
        &options(CompilationBackend::Rust),
    )
    .unwrap_or_else(|error| panic!("the kinds definition loads: {error}"))
    .0;
    let mut definition = loaded.definition.clone();
    let module = definition
        .modules
        .iter_mut()
        .find(|module| module.name == "KINDS")
        .unwrap();
    let mut found = Vec::new();
    for sentence in &mut module.local_sentences {
        let sentence = k_rust::definition::sentence_mut(sentence);
        let kind = kind_of(sentence);
        for term in rule_like_terms(sentence) {
            visit_labels(term, &mut |label| {
                if ["wrap", "box", "cl", "cx", "al"].contains(&label.name.as_str()) {
                    found.push((kind, label.to_string()));
                }
            });
        }
    }
    found.sort_unstable();
    found.dedup();
    assert_eq!(
        found,
        [
            ("claim", "cl".to_owned()),
            ("context", "cx".to_owned()),
            ("context alias", "al".to_owned()),
            ("rule", "box".to_owned()),
            ("rule", "wrap".to_owned()),
        ]
    );

    let parsed = parse_rule_content(
        &loaded.resolved,
        "KINDS",
        "f(X:Nat) => wrap(X)",
        Attributes::default(),
    )
    .unwrap();
    let mut parsed = std::sync::Arc::new(parsed);
    let mut labels = Vec::new();
    for term in rule_like_terms(k_rust::definition::sentence_mut(&mut parsed)) {
        visit_labels(term, &mut |label| labels.push(label.to_string()));
    }
    assert!(labels.contains(&"wrap".to_owned()), "{labels:?}");
    assert!(
        labels.iter().all(|label| !label.contains('{')),
        "{labels:?}"
    );
}

/// The instance each parametric label of `PARAMS` had when the parser wrote its own choice into
/// the loaded label: `wrap` realised its unconstrained parameter as `K`, `ite` took `Int`, and
/// `#Equals` took `K` for both parameters.
fn hand_written_parameters(label: &Label) -> Option<Vec<Sort>> {
    match label.name.as_str() {
        "wrap" => Some(vec![Sort::new("K")]),
        "ite" => Some(vec![Sort::new("Int")]),
        "#Equals" => Some(vec![Sort::new("K"), Sort::new("K")]),
        _ => None,
    }
}

/// The source definition compiles to the same three KORE files as its loaded definition passed
/// back through `load_structured` with the parser's former parameters written into the user
/// modules by hand: a label parameter on a loaded rule-like term never reached the emitted KORE,
/// so dropping it at the bubble boundary changes no output.
#[test]
fn source_kore_equals_structured_kore_with_hand_written_parameters() {
    for backend in BACKENDS {
        let source = load_source(backend);
        let expected = compile(&source, backend);

        let mut structured = source.definition.clone();
        let mut written = 0usize;
        for module in structured
            .modules
            .iter_mut()
            .filter(|module| USER_MODULES.contains(&module.name.as_str()))
        {
            for_each_rule_like_label(module, |label| {
                if let Some(parameters) = hand_written_parameters(label) {
                    label.parameters = parameters;
                    written += 1;
                }
            });
        }
        assert_eq!(written, 4, "{backend}: wrap, ite, #Equals x2");

        let loaded = load_structured(
            structured,
            &LoadOptions {
                excluded_module_attributes: vec![backend.excluded_module_attribute().to_owned()],
                ..LoadOptions::default()
            },
        )
        .unwrap_or_else(|error| panic!("{backend}: structured loading: {error}"));
        let actual = compile(&loaded, backend);
        for (index, name) in ["definition.kore", "syntaxDefinition.kore", "macros.kore"]
            .into_iter()
            .enumerate()
        {
            assert!(
                actual[index] == expected[index],
                "{backend}: {name} differs between the source and the hand-written parameters"
            );
        }
    }
}
