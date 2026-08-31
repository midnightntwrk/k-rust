//! One continuous KRS-authored expression route for NR-07Q-T2.

use std::path::PathBuf;

use k::Term;
use k::builtin::Bool;
use k_rust::{
    definition::Sentence as NativeSentence, kast::Term as NativeTerm,
    kore::parser::parse_definition as parse_kore_definition,
};
use krs_compiler::{
    PackageContext, collect_host_descriptors_with_builtins, lower_descriptor_bundle,
    lower_semantic_theory,
};
use krs_ir::{
    DefinitionSentence, DefinitionTerm, DefinitionTermKind, ItemKind, NodeOrigin, OriginFrame,
    RangedOriginKind, SemanticTerm, SemanticTermKind,
};
use krs_k_rust::{
    Backend, CompileOptions, NativeNodeRole, adapt_definition, compile_loaded_definition,
    prepare_definition,
};

#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait KResult {}

#[k::sort]
pub trait Expr {}

#[k::sort]
pub trait Value: Expr + KResult {}

impl KItem for Bool {}
impl KResult for Bool {}
impl Expr for Bool {}

#[k::subsort]
impl Value for Bool {}

#[k::constructor(sort = Expr, syntax = "{lhs} && {rhs}")]
pub struct And {
    pub lhs: Term<dyn Expr>,
    pub rhs: Term<dyn Expr>,
}

#[k::configuration]
pub struct Machine {
    pub k: k::configuration::KCell<k::builtin::KSequence>,
}

#[allow(clippy::must_use_candidate, clippy::needless_pass_by_value)]
impl Machine {
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] program: Term<dyn Expr>) -> Self {
        Self {
            k: k::configuration::KCell::new(k::k![program]),
        }
    }
}

#[k::rule]
pub fn and_true(And { lhs: true, rhs }: Term<dyn Expr>) -> Term<dyn Expr> {
    rhs
}

fn authored_text(origin: &NodeOrigin) -> &'static str {
    let range = origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged {
                kind: RangedOriginKind::Authored,
                range,
                ..
            } => Some(range),
            OriginFrame::Ranged { .. } | OriginFrame::Transformation { .. } => None,
        })
        .expect("every selected expression node has an authored range");
    assert_eq!(range.file.package_relative_path(), "src/main.rs");
    let source = include_str!("main.rs");
    source
        .get(range.start_byte as usize..range.end_byte as usize)
        .expect("KRS authored ranges are UTF-8 boundaries in this fixture")
}

fn semantic_expression_nodes(
    body: &SemanticTerm,
) -> (&SemanticTerm, &SemanticTerm, &SemanticTerm, &SemanticTerm) {
    let SemanticTermKind::Rewrite { from, to } = body.kind() else {
        panic!("and_true must remain one semantic rewrite")
    };
    let SemanticTermKind::Application { arguments, .. } = from.kind() else {
        panic!("and_true lhs must remain an application")
    };
    let [literal, reference] = arguments.as_slice() else {
        panic!("and_true application must retain its two authored arguments")
    };
    assert!(matches!(literal.kind(), SemanticTermKind::Token { value } if value == "true"));
    assert!(matches!(
        reference.kind(),
        SemanticTermKind::Variable { .. }
    ));
    assert!(matches!(to.kind(), SemanticTermKind::Variable { .. }));
    (from, literal, reference, to)
}

fn definition_expression_nodes(
    body: &DefinitionTerm,
) -> (
    &DefinitionTerm,
    &DefinitionTerm,
    &DefinitionTerm,
    &DefinitionTerm,
) {
    let DefinitionTermKind::Rewrite { from, to } = body.kind() else {
        panic!("and_true must remain one Definition-IR rewrite")
    };
    let DefinitionTermKind::Application { arguments, .. } = from.kind() else {
        panic!("and_true Definition-IR lhs must remain an application")
    };
    let [literal, reference] = arguments.as_slice() else {
        panic!("and_true Definition-IR application must retain two arguments")
    };
    assert!(matches!(literal.kind(), DefinitionTermKind::Token { value } if value == "true"));
    assert!(matches!(
        reference.kind(),
        DefinitionTermKind::Variable { .. }
    ));
    assert!(matches!(to.kind(), DefinitionTermKind::Variable { .. }));
    (from, literal, reference, to)
}

fn main() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    let context = PackageContext::new(
        "KINK-NR-07Q-T2",
        env!("CARGO_PKG_NAME"),
        env!("CARGO_PKG_VERSION"),
        "workspace",
        module_path!(),
        manifest,
    )
    .expect("the downstream fixture package context is valid");

    let descriptors = k::host_descriptors().collect::<Vec<_>>();
    let bundle =
        collect_host_descriptors_with_builtins([context], descriptors, &k::builtin_registry())
            .expect("the exact authored Rust source parses and its descriptors collect");
    let descriptor = bundle
        .descriptors
        .iter()
        .find(|descriptor| {
            descriptor.id.item_kind() == ItemKind::Rule && descriptor.id.item_name() == "and_true"
        })
        .expect("and_true has one collected stable rule descriptor");
    assert!(
        descriptor.provenance.origins().iter().any(|node| node
            .origin
            .frames()
            .iter()
            .any(OriginFrame::is_authored))
    );

    let semantic = lower_descriptor_bundle(&bundle)
        .expect("the collected artifact lowers to checked Semantic IR");
    let semantic_rule = semantic
        .modules()
        .iter()
        .flat_map(krs_ir::SemanticModule::rules)
        .find(|rule| rule.id() == &descriptor.id)
        .expect("the same stable and_true rule reaches Semantic IR");
    let semantic_body = semantic_rule
        .body()
        .expect("and_true has an ordinary semantic term body");
    let (semantic_application, semantic_literal, semantic_reference, semantic_result) =
        semantic_expression_nodes(semantic_body);
    assert_eq!(authored_text(semantic_application.origin()), "And");
    assert_eq!(authored_text(semantic_literal.origin()), "true");
    assert_eq!(authored_text(semantic_reference.origin()), "rhs");
    assert_eq!(authored_text(semantic_result.origin()), "rhs");

    let lowered = lower_semantic_theory(&semantic)
        .expect("the same Semantic IR artifact lowers to checked Definition IR");
    let definition_rule = lowered
        .definition()
        .modules()
        .iter()
        .flat_map(krs_ir::DefinitionModule::sentences)
        .find_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule)
                if rule.origin().origin().frames().iter().any(|frame| {
                    matches!(frame, OriginFrame::Transformation { item: Some(item), .. }
                        if item == &descriptor.id)
                }) =>
            {
                Some(rule)
            }
            DefinitionSentence::SyntaxSort(_)
            | DefinitionSentence::Subsort(_)
            | DefinitionSentence::Production(_)
            | DefinitionSentence::Precedence(_)
            | DefinitionSentence::Associativity(_)
            | DefinitionSentence::Configuration(_)
            | DefinitionSentence::ContextAlias(_)
            | DefinitionSentence::Rule(_) => None,
        })
        .expect("and_true stable identity remains in its Definition-IR provenance");
    let definition_body = definition_rule
        .body()
        .expect("and_true has an ordinary Definition-IR term body");
    let (definition_application, definition_literal, definition_reference, definition_result) =
        definition_expression_nodes(definition_body);
    for (node, expected) in [
        (definition_application, "And"),
        (definition_literal, "true"),
        (definition_reference, "rhs"),
        (definition_result, "rhs"),
    ] {
        assert_eq!(authored_text(node.origin()), expected);
    }

    let adapted = adapt_definition(lowered.definition())
        .expect("the same checked Definition IR adapts to the native source model");
    let mapping = |node: &DefinitionTerm, path: &[u32]| {
        adapted
            .origins()
            .iter()
            .find(|mapping| {
                mapping.key == *node.origin().key()
                    && mapping.origin == *node.origin()
                    && matches!(&mapping.role, NativeNodeRole::Term(actual) if actual == path)
            })
            .expect("each selected Definition term has its exact structural native mapping")
    };
    let application_mapping = mapping(definition_application, &[0]);
    mapping(definition_literal, &[0, 0]);
    mapping(definition_reference, &[0, 1]);
    mapping(definition_result, &[1]);
    let sentence_mapping = adapted
        .origins()
        .iter()
        .find(|mapping| {
            mapping.key == *definition_rule.origin().key()
                && mapping.origin == *definition_rule.origin()
                && mapping.role == NativeNodeRole::Sentence
        })
        .expect("the and_true sentence has its exact structural native mapping");
    assert_eq!(application_mapping.module, sentence_mapping.module);
    assert_eq!(
        application_mapping.sentence_index,
        sentence_mapping.sentence_index
    );

    let native_module = adapted
        .definition()
        .modules
        .iter()
        .find(|module| module.name == sentence_mapping.module)
        .expect("the mapped native module exists");
    let native_sentence = &native_module.local_sentences[sentence_mapping
        .sentence_index
        .expect("sentence mappings carry a local index")];
    let NativeSentence::Rule { body, .. } = native_sentence else {
        panic!("the mapped native sentence remains a rule")
    };
    let NativeTerm::Rewrite { left, right } = body.unannotated() else {
        panic!("the mapped native body remains a rewrite")
    };
    let NativeTerm::Apply { arguments, .. } = left.unannotated() else {
        panic!("the mapped native lhs remains an application")
    };
    let [literal, reference] = arguments.as_slice() else {
        panic!("the mapped native application keeps exactly two arguments")
    };
    assert!(matches!(
        literal.unannotated(),
        NativeTerm::Token { token, .. } if token == "true"
    ));
    let NativeTerm::Variable {
        name: reference_name,
        ..
    } = reference.unannotated()
    else {
        panic!("the mapped native reference remains a variable")
    };
    let NativeTerm::Variable {
        name: result_name, ..
    } = right.unannotated()
    else {
        panic!("the mapped native result remains a variable")
    };
    assert!(!reference_name.is_empty());
    assert_eq!(reference_name, result_name);

    let options = CompileOptions {
        backend: Backend::Llvm,
        ..CompileOptions::default()
    };
    let loaded = prepare_definition(adapted.definition().clone(), options.backend)
        .expect("the exact adapted native value prepares through public pinned APIs");
    let artifacts = compile_loaded_definition(&loaded, options)
        .expect("the exact prepared native value compiles through the public frontend");
    let definition_kore = parse_kore_definition(&artifacts.definition_kore)
        .expect("the pinned public parser reparses definition.kore");
    let syntax_kore = parse_kore_definition(&artifacts.syntax_definition_kore)
        .expect("the pinned public parser reparses syntaxDefinition.kore");
    assert!(!definition_kore.modules.is_empty());
    assert!(!syntax_kore.modules.is_empty());

    println!(
        "PASS NR-07Q-T2 continuous cases=application,literal,reference stages=9 provenance=sidecar-only-missing-bridge authority=false"
    );
}
