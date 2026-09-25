//! Label sort parameters on loaded rule-like sentences.
//!
//! K source text cannot write a label parameter, so a source-loaded rule, claim, context,
//! context alias or configuration carries none: sort injection solves every parametric label
//! from its arguments and position. A parameter a caller writes is rejected at compilation and
//! by the typing view, whatever the entry path; a cast fixes an instance instead.

use k_rust::builtin;
use k_rust::definition::Attributes;
use k_rust::definition::{Definition, FlatModule, Sentence};
use k_rust::inner::parse_rule_content;
use k_rust::kast::{Label, Sort, Term};
use k_rust::kompile::{
    CompilationBackend, CompileError, CompileOptions, REJECT_LABEL_PARAMETERS,
    compile_loaded_definition,
};
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

/// A loaded rule's `m()` carries no instance: macro expansion, which runs before sort injection,
/// takes it from the position, so each function's body expands by the macro rule stated for its
/// result sort, not by the first rule of `m`.
#[test]
fn a_parametric_macro_in_a_rule_expands_by_its_position() {
    let source = r#"
module MACROS
  imports INT
  imports BOOL
  syntax {S} S ::= m() [macro, symbol(m)]
  rule m():Int => 1
  rule m():Bool => true
  syntax Bool ::= f() [function, symbol(f)]
  rule f() => m()
  syntax Int ::= g() [function, symbol(g)]
  rule g() => m()
  syntax Int ::= h(Int) [function, symbol(h)]
  rule h(_) => 0 requires m()
endmodule
"#;
    for backend in BACKENDS {
        let mut resolver = |_: &str, required: &str| {
            builtin::embedded(required).ok_or_else(|| required.to_owned())
        };
        let loaded = load_for_compilation(
            ResolvedSource::new("macros.k", source.to_owned()),
            "MACROS",
            Some("MACROS"),
            &mut resolver,
            &options(backend),
        )
        .unwrap_or_else(|error| panic!("{backend}: the macros definition loads: {error}"))
        .0;
        let [definition_kore, ..] = compile(&loaded, backend);
        for expected in [
            r#"\equals{SortBool{}, R}(
        Lblf{}(),
        \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}())"#,
            r#"\equals{SortInt{}, R}(Lblg{}(), \and{SortInt{}}(\dv{SortInt{}}("1"), \top{SortInt{}}()))"#,
        ] {
            assert!(definition_kore.contains(expected), "{backend}: {expected}");
        }
    }
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

fn load_structured_for(definition: Definition, backend: CompilationBackend) -> LoadedDefinition {
    load_structured(
        definition,
        &LoadOptions {
            excluded_module_attributes: vec![backend.excluded_module_attribute().to_owned()],
            ..LoadOptions::default()
        },
    )
    .unwrap_or_else(|error| panic!("{backend}: structured loading: {error}"))
}

fn try_compile(
    loaded: &LoadedDefinition,
    backend: CompilationBackend,
) -> Result<[String; 3], CompileError> {
    compile_loaded_definition(
        loaded,
        CompileOptions {
            backend,
            ..CompileOptions::default()
        },
    )
    .map(|artifacts| {
        [
            artifacts.definition_kore,
            artifacts.syntax_definition_kore,
            artifacts.macros_kore,
        ]
    })
}

fn assert_rejects_label_parameters(error: &CompileError, label: &str, parameters: &str) {
    assert_eq!(error.stage, REJECT_LABEL_PARAMETERS, "{error}");
    assert!(
        error.message.contains(&format!(
            "KLabel {label:?} carries the sort parameters {{{parameters}}}"
        )),
        "{error}"
    );
    assert!(
        error
            .message
            .contains("remove them, or use a cast to fix an instance"),
        "{error}"
    );
}

/// The source definition compiles through `load_structured` to the same three KORE files; with
/// the parser's former parameters written into its labels by hand, every structured load is
/// rejected instead of having the parameters re-solved.
#[test]
fn structured_parameters_the_parser_used_to_write_are_rejected() {
    for backend in BACKENDS {
        let source = load_source(backend);
        let expected = compile(&source, backend);
        let round_trip = compile(
            &load_structured_for(source.definition.clone(), backend),
            backend,
        );
        assert!(round_trip == expected, "{backend}: structured round trip");

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
        let error = try_compile(&load_structured_for(structured, backend), backend)
            .expect_err("a written label parameter is rejected");
        assert_rejects_label_parameters(&error, "wrap", "K");
    }
}

/// Rejection on each entry path over a definition whose `MInt{8}` rule needs native Z3 sort
/// inference to parse.
#[cfg(feature = "z3-inference")]
mod native {
    use super::*;
    use k_rust::definition::ResolvedDefinition;
    use k_rust::kompile::{SentenceTypingError, SortInjectionError, sentence_typing};

    /// A user parametric production whose parameter occurs in an argument (`wrap`, `use`), and one
    /// whose parameter occurs in neither an argument nor the result (`size`).
    const REJECT_SOURCE: &str = r#"
    requires "domains.md"

    module REJECT-SYNTAX
      imports DOMAINS-SYNTAX
    endmodule

    module REJECT
      imports DOMAINS
      imports MINT
      syntax MInt{8}
      syntax Nat ::= "z" [symbol(z)] | s(Nat) [symbol(s)]
      syntax Num ::= Nat
      syntax {S} Wrap ::= wrap(S) [symbol(wrap)]
      syntax Wrap ::= f(Nat) [function, symbol(f)]
                    | fUp(Nat) [function, symbol(fUp)]
                    | fProj(Nat) [function, symbol(fProj)]
      syntax {W} Bool ::= use(MInt{W}) [function, total, symbol(use)]
      syntax Bool ::= u8(MInt{8}) [function, symbol(u8)]
      syntax {S} Int ::= size() [function, total, symbol(size)]
      syntax Int ::= g() [function, symbol(g)]
      rule [wrapping]: f(X:Nat) => wrap(X)
      rule [upcast]: fUp(X:Nat) => wrap(s(X):Num)
      rule [projected]: fProj(X:Nat) => wrap({X}:>Num)
      rule [use8]: u8(X:MInt{8}) => use(X)
      rule [sized]: size() => 0
      rule [phantom]: g() => size()
    endmodule
    "#;

    fn load_reject_source() -> LoadedDefinition {
        let mut resolver = |_: &str, required: &str| {
            builtin::embedded(required).ok_or_else(|| required.to_owned())
        };
        load_for_compilation(
            ResolvedSource::new("reject.k", REJECT_SOURCE.to_owned()),
            "REJECT",
            None,
            &mut resolver,
            &options(CompilationBackend::Rust),
        )
        .unwrap_or_else(|error| panic!("the reject definition loads: {error}"))
        .0
    }

    /// `definition` with `parameters` written into the label `name` of the rule labelled `rule`.
    fn with_written_parameters(
        definition: &Definition,
        rule: &str,
        name: &str,
        parameters: &[&str],
    ) -> (Definition, Sentence) {
        let mut definition = definition.clone();
        let module = definition
            .modules
            .iter_mut()
            .find(|module| module.name == "REJECT")
            .unwrap();
        let sentence = module
            .local_sentences
            .iter_mut()
            .find(|sentence| {
                sentence
                    .attributes()
                    .string(k_rust::definition::AttributeKey::Label)
                    == Some(&format!("REJECT.{rule}"))
            })
            .unwrap_or_else(|| panic!("rule {rule}"));
        let sentence = k_rust::definition::sentence_mut(sentence);
        let mut written = 0usize;
        for term in rule_like_terms(sentence) {
            visit_labels(term, &mut |label| {
                if label.name == name {
                    label.parameters = parameters.iter().map(|sort| Sort::new(*sort)).collect();
                    written += 1;
                }
            });
        }
        assert_eq!(written, 1, "{rule} applies {name} once");
        let sentence = sentence.clone();
        (definition, sentence)
    }

    /// Without a written parameter, each instance is the one sort injection solves: the least one
    /// fitting the arguments and the position. An upcast on an argument does not raise it
    /// (`wrap(s(X):Num)` is `wrap{Nat}`); an instance above the argument's sort is reached only
    /// through a projection (`wrap({X}:>Num)` is `wrap{Num}` of `project:Num`), as in K source. A
    /// parameter occurring in neither an argument nor the result (`size`'s `S`) is universally
    /// quantified in every sentence that uses it. A written parameter is rejected on each entry
    /// path: a structured load, a hand-built `LoadedDefinition`, and the typing view. The `MInt{8}`
    /// rule needs native Z3 sort inference to parse.
    #[test]
    fn a_written_label_parameter_is_rejected_and_the_solved_instance_is_emitted() {
        let backend = CompilationBackend::Rust;
        let source = load_reject_source();
        let [definition_kore, ..] = try_compile(&source, backend)
            .unwrap_or_else(|error| panic!("the parameter-free definition compiles: {error}"));
        for expected in [
            "Lblwrap{SortNat{}}(VarX:SortNat{})",
            "Lblwrap{SortNat{}}(Lbls{}(VarX:SortNat{}))",
            "Lblwrap{SortNum{}}(\n            Lblproject'Coln'Num{}(",
            "Lbluse{Sort8{}}(VarX:SortMInt{Sort8{}})",
            "Lblsize{Sort'Hash'SortParam{",
        ] {
            assert!(definition_kore.contains(expected), "{expected}");
        }
        assert!(!definition_kore.contains("Lblsize{SortNat{}}"));

        for (rule, name, parameters, rendered) in [
            ("wrapping", "wrap", &["Num"][..], "Num"),
            ("use8", "use", &["16"][..], "16"),
            ("phantom", "size", &["Nat"][..], "Nat"),
        ] {
            let (edited, sentence) =
                with_written_parameters(&source.definition, rule, name, parameters);

            let structured = load_structured_for(edited.clone(), backend);
            let error = try_compile(&structured, backend).expect_err(rule);
            assert_rejects_label_parameters(&error, name, rendered);

            let hand_built = LoadedDefinition {
                files: source.files.clone(),
                source_table: source.source_table.clone(),
                resolved: ResolvedDefinition::resolve(&edited).unwrap(),
                definition: edited,
                diagnostics: source.diagnostics.clone(),
            };
            let error = try_compile(&hand_built, backend).expect_err(rule);
            assert_rejects_label_parameters(&error, name, rendered);

            let error = sentence_typing(&hand_built.resolved, "REJECT", &sentence).expect_err(rule);
            let SentenceTypingError::Sort {
                error: SortInjectionError::LabelParameters { label, parameters },
                ..
            } = error
            else {
                panic!("{rule}: {error}")
            };
            assert_eq!(label, name);
            assert_eq!(parameters, [Sort::new(rendered)]);
        }
    }
}
