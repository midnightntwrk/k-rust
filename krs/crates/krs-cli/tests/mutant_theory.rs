//! The theory check of a mutation (`krs_compiler::MutantTheory`): KRS's rule-level admission
//! checks on the specification's pre-derivation theory with the mutation's changes, over
//! packages lowered in process as `krs emit-k` lowers them. Changing nothing, and replacing every
//! sentence by itself, is admitted, since the specification is; deleting a member of a two-rule
//! nondet group is KRS's `nondet-group` refusal, naming the member left; a key that names no
//! rule, and an edit of a clause the static rewriting reads, are not checked.

use std::fs;
use std::path::{Path, PathBuf};

use krs_compiler::{MutantTheory, TheoryChanges, TheoryCheckError, rule_sentence_key};
use krs_ir::SentenceKind;
use krs_test_support::{shared_fixture_target, temp_dir};

/// The definition of the front end's mutation checks, with its nondet group.
const CHECKED: &str = include_str!("fixtures/kink-checks/src/lib.rs");
/// A definition with a desugar clause.
const INSERTED: &str = include_str!("fixtures/inserted-nodes/src/lib.rs");

fn package(root: &Path, name: &str, namespace: &str, library: &str) -> PathBuf {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"{namespace}\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            serde_json::to_string(krs.to_str().unwrap()).unwrap(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// The lowering of the `main` definition of a package holding `library`, kept in process.
fn retained(name: &str, namespace: &str, library: &str) -> krs_compiler::RetainedLowering {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), name, namespace, library);
    let request = krs_cli::CommandRequest {
        command: krs_cli::Command::Check {
            backend: None,
            partition: false,
        },
        manifest_path: manifest,
        root: krs_cli::FacetSelector {
            package: krs_cli::PackageSelector::Name(name.into()),
            definition: "main".into(),
        },
        dependencies: Vec::new(),
        cfg: Vec::new(),
        registration: krs_cli::RegistrationMode::Inventory,
        no_reuse: true,
        message_format: krs_cli::MessageFormat::Human,
        profile: None,
    };
    let collected = krs_cli::collect_descriptors(&request, Some(target.path())).unwrap();
    collected
        .emit_k_retained(collected.bundle.clone())
        .unwrap()
        .retained
}

#[test]
fn the_theory_check_is_krs_admission_of_the_changed_theory() {
    let retained = retained("krs-cli-mutant-theory", "CHECKS", CHECKED);
    let theory = MutantTheory::new(&retained);
    assert!(matches!(
        theory.check(&TheoryChanges::default()),
        Ok(Ok(()))
    ));
    let rules = retained
        .admitted()
        .iter()
        .flat_map(krs_ir_levels::SemanticModule::rules)
        .collect::<Vec<_>>();
    let itself = TheoryChanges {
        replaced: rules
            .iter()
            .map(|rule| (rule_sentence_key(rule).clone(), (*rule).clone()))
            .collect(),
        deleted: std::collections::BTreeSet::default(),
    };
    assert!(
        matches!(theory.check(&itself), Ok(Ok(()))),
        "every sentence replaced by itself is the specification"
    );
    let named = |item: &str| {
        rules
            .iter()
            .find(|rule| rule.id().item_name() == item)
            .unwrap_or_else(|| panic!("no rule {item}"))
    };
    let tails = rule_sentence_key(named("toss_tails")).clone();
    let deleted = TheoryChanges {
        replaced: std::collections::BTreeMap::default(),
        deleted: [tails.clone()].into(),
    };
    let refusal = match theory.check(&deleted) {
        Ok(Err(refusal)) => refusal,
        other => panic!("deleting a member of a two-rule group is refused: {other:?}"),
    };
    assert_eq!(refusal.code, "krs::analysis::nondet-group");
    assert_eq!(
        refusal
            .items
            .iter()
            .map(krs_ir::StableItemId::item_name)
            .collect::<Vec<_>>(),
        ["toss_heads"]
    );
    assert_eq!(
        refusal.sentences,
        [rule_sentence_key(named("toss_heads")).clone()]
    );
    assert!(
        refusal.message.contains("nondet group `toss`"),
        "{}",
        refusal.message
    );
    // A key no rule of the theory has: the module's own.
    let module = retained.admitted()[0].origin().key().clone();
    assert_eq!(
        theory
            .check(&TheoryChanges {
                replaced: std::collections::BTreeMap::default(),
                deleted: [module.clone()].into(),
            })
            .err(),
        Some(TheoryCheckError::UnknownSentence(module))
    );
}

#[test]
fn an_edit_of_a_clause_the_static_rewriting_reads_is_not_checked() {
    let retained = retained(
        "krs-cli-mutant-theory-statics",
        "ORG-KRS-INSERTED",
        INSERTED,
    );
    let theory = MutantTheory::new(&retained);
    let clause = retained
        .admitted()
        .iter()
        .flat_map(krs_ir_levels::SemanticModule::rules)
        .find(|rule| rule.kind() == SentenceKind::Desugar)
        .expect("the fixture has a desugar clause");
    let key = rule_sentence_key(clause).clone();
    let changes = TheoryChanges {
        replaced: [(key.clone(), clause.clone())].into(),
        deleted: std::collections::BTreeSet::default(),
    };
    assert_eq!(
        theory.check(&changes).err(),
        Some(TheoryCheckError::StaticClause(key))
    );
}
