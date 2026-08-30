//! Host collection integration tests.

use std::any::TypeId;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use krs_compiler::{CollectionErrorKind, PackageContext, collect_host_descriptors};
use krs_ir::{
    AnchorPrecision, BuiltinSort, ConfigurationCellDescriptor, HostAuthoredAnchor,
    HostConfigurationDescriptor, HostConfigurationInitializerDescriptor,
    HostConfigurationVariableDescriptor, HostConstructorDescriptor, HostConstructorFieldDescriptor,
    HostDescriptor, HostDescriptorPayload, HostDescriptorReference, HostItemId, HostPackageKey,
    HostProvenance, HostRuleDescriptor, HostRuleParameterDescriptor, HostSortDescriptor,
    HostSourceAnchor, HostSourcePosition, HostTypeKey, HostTypeReference, ItemKind,
    ProtocolVersion, RustVisibility, SentenceKind,
};
use krs_syntax::{
    ConfigurationDeclaration, ConstructorDeclaration, InitializerFunction, ProvenanceAnchor,
    ProvenanceRole, RuleItem, SortDeclaration, parse_configuration_attribute,
    parse_constructor_attribute, parse_symbol_attribute,
};
use sha2::{Digest, Sha256};
use syn::{ImplItem, Item, Meta};

fn attribute_named(attribute: &syn::Attribute, name: &str) -> bool {
    attribute
        .path()
        .segments
        .last()
        .is_some_and(|segment| segment.ident == name)
}

fn attribute_tokens(attribute: &syn::Attribute) -> proc_macro2::TokenStream {
    match &attribute.meta {
        Meta::Path(_) => proc_macro2::TokenStream::new(),
        Meta::List(list) => list.tokens.clone(),
        Meta::NameValue(_) => panic!("KRS attributes do not use name-value syntax"),
    }
}

struct KItemType;
struct ExprType;
struct FooType;
struct BarType;
struct KResultType;
struct M2ObjType;
struct OtherType;
struct MachineType;

fn kitem_type() -> TypeId {
    TypeId::of::<KItemType>()
}

fn expr_type() -> TypeId {
    TypeId::of::<ExprType>()
}

fn foo_type() -> TypeId {
    TypeId::of::<FooType>()
}

fn bar_type() -> TypeId {
    TypeId::of::<BarType>()
}

fn kresult_type() -> TypeId {
    TypeId::of::<KResultType>()
}

fn m2obj_type() -> TypeId {
    TypeId::of::<M2ObjType>()
}

fn other_type() -> TypeId {
    TypeId::of::<OtherType>()
}

fn machine_type() -> TypeId {
    TypeId::of::<MachineType>()
}

#[test]
fn collection_is_deterministic_and_resolves_all_m1_reference_shapes() {
    let package = TestPackage::new(
        "semantics",
        r#"#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::constructor(sort = Expr, syntax = "foo({value})")]
pub struct Foo { pub value: Term<dyn Expr> }

#[k::rule]
fn step(Foo(value): Term<dyn Expr>) -> Term<dyn Expr> {
    term!(Foo(value))
}
"#,
    );
    let descriptors = vec![
        package.sort("KItem", kitem_type, vec![]),
        package.sort("Expr", expr_type, vec![type_ref(kitem_type, "KItem")]),
        package.constructor("Foo", foo_type, expr_type),
        package.rule("step", expr_type, foo_type),
    ];

    let first =
        collect_host_descriptors([package.context("ORG-SEMANTICS")], descriptors.clone()).unwrap();
    let second = collect_host_descriptors(
        [package.context("ORG-SEMANTICS")],
        descriptors.into_iter().rev(),
    )
    .unwrap();

    assert_eq!(first, second);
    assert_eq!(first.descriptors.len(), 4);
    let json = first.to_canonical_json().unwrap();
    assert!(!json.contains(package.root().to_str().unwrap()));
    assert!(json.contains("rule_left_path"));
    assert!(json.contains("rule_right_path"));
    assert!(json.contains("content_sha256"));
}

#[test]
fn collection_preserves_exact_visibility_and_explicit_symbol_provenance() {
    let package = TestPackage::new(
        "stable_api",
        r#"#[k::symbol("api::Expr")]
#[k::sort]
pub trait Expr {}

#[k::symbol("api::PublicValue")]
#[k::constructor(sort = Expr, syntax = "publicValue")]
pub struct PublicValue;
"#,
    );
    let bundle = collect_host_descriptors(
        [package.context("ORG-STABLE-API")],
        [
            package.sort("Expr", expr_type, vec![]),
            package.constructor("PublicValue", foo_type, expr_type),
        ],
    )
    .unwrap();
    let expr = bundle
        .declarations
        .iter()
        .find(|declaration| declaration.id().item_name() == "Expr")
        .unwrap();
    assert_eq!(expr.visibility, RustVisibility::Public);
    assert_eq!(expr.explicit_symbol.as_ref().unwrap().as_str(), "api::Expr");
    let value = bundle
        .declarations
        .iter()
        .find(|declaration| declaration.id().item_name() == "PublicValue")
        .unwrap();
    assert_eq!(value.visibility, RustVisibility::Public);
    assert_eq!(
        value.explicit_symbol.as_ref().unwrap().as_str(),
        "api::PublicValue"
    );
    for descriptor in &bundle.descriptors {
        assert!(
            descriptor.provenance.origins().iter().any(|origin| {
                origin.key.role() == "stable_symbol" && origin.key.ordinal() == 0
            })
        );
    }
}

#[test]
fn unicode_scalar_anchors_materialize_exact_utf8_byte_ranges() {
    let package = TestPackage::new(
        "unicode_semantics",
        "const 日本: () = ();\n#[k::sort]\npub trait Expr {}\n",
    );
    let bundle = collect_host_descriptors(
        [package.context("ORG-UNICODE")],
        [package.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    let authored = &bundle.descriptors[0].origin().frames()[0];
    let krs_ir::OriginFrame::Ranged { range, .. } = authored else {
        panic!("first frame must be authored")
    };
    let source = fs::read_to_string(package.root().join("src/lib.rs")).unwrap();
    assert_eq!(
        &source[range.start_byte as usize..range.end_byte as usize],
        "Expr"
    );
}

#[test]
fn canonical_manifest_matching_accepts_a_symlink_hint() {
    let package = TestPackage::new("linked", "#[k::sort]\npub trait Expr {}\n");
    let link = package.root().with_extension("link");
    #[cfg(unix)]
    std::os::unix::fs::symlink(package.root(), &link).unwrap();
    #[cfg(windows)]
    std::os::windows::fs::symlink_dir(package.root(), &link).unwrap();
    let mut descriptor = package.sort("Expr", expr_type, vec![]);
    descriptor.id = HostItemId::new(
        HostPackageKey::new("linked", "0.1.0", &link).unwrap(),
        ["linked"],
        "Expr",
        ItemKind::Sort,
        "",
    )
    .unwrap();
    let result = collect_host_descriptors([package.context("ORG-LINK")], [descriptor]);
    fs::remove_file(&link).unwrap();
    assert!(result.is_ok());
}

#[test]
fn same_names_in_modules_and_packages_remain_distinct() {
    let source = r"pub mod left {
    #[k::sort]
    pub trait Value {}
}
pub mod right {
    #[k::sort]
    pub trait Value {}
}
";
    let first = TestPackage::new("first", source);
    let second = TestPackage::new("second", "#[k::sort]\npub trait Value {}\n");
    let descriptors = [
        first.sort_in_module("Value", 0, "left", expr_type),
        first.sort_in_module("Value", 1, "right", other_type),
        second.sort("Value", kitem_type, vec![]),
    ];
    let bundle = collect_host_descriptors(
        [first.context("ORG-FIRST"), second.context("ORG-SECOND")],
        descriptors.clone(),
    )
    .unwrap();
    let reordered = collect_host_descriptors(
        [second.context("ORG-SECOND"), first.context("ORG-FIRST")],
        descriptors.into_iter().rev(),
    )
    .unwrap();
    assert_eq!(bundle, reordered);
    assert_eq!(bundle.descriptors.len(), 3);
    assert_ne!(bundle.descriptors[0].id, bundle.descriptors[1].id);
    assert_ne!(bundle.descriptors[1].id, bundle.descriptors[2].id);
}

#[test]
fn changed_semantic_source_is_rejected_as_stale() {
    let package = TestPackage::new("changed", "#[k::sort]\npub trait Expr {}\n");
    let descriptor = package.sort("Expr", expr_type, vec![]);
    fs::write(
        package.root().join("src/lib.rs"),
        "#[k::sort]\npub trait Changed {}\n",
    )
    .unwrap();
    let error =
        collect_host_descriptors([package.context("ORG-CHANGED")], [descriptor]).unwrap_err();
    assert_eq!(error.kind(), CollectionErrorKind::StaleAnchor);
}

#[test]
fn rejects_protocol_root_duplicate_id_and_duplicate_type() {
    let package = TestPackage::new("negative", "#[k::sort]\npub trait Expr {}\n");

    let mut old = package.sort("Expr", expr_type, vec![]);
    old.protocol_version = ProtocolVersion(2);
    assert_kind(
        collect_host_descriptors([package.context("ORG-NEG")], [old]),
        CollectionErrorKind::UnsupportedProtocol,
    );

    let mut wrong_root = package.sort("Expr", expr_type, vec![]);
    wrong_root.id = HostItemId::new(
        HostPackageKey::new("negative", "0.1.0", package.root()).unwrap(),
        ["not_negative"],
        "Expr",
        ItemKind::Sort,
        "",
    )
    .unwrap();
    assert_kind(
        collect_host_descriptors([package.context("ORG-NEG")], [wrong_root]),
        CollectionErrorKind::CrateRootMismatch,
    );

    let duplicate = package.sort("Expr", expr_type, vec![]);
    assert_kind(
        collect_host_descriptors([package.context("ORG-NEG")], [duplicate.clone(), duplicate]),
        CollectionErrorKind::DuplicateItemId,
    );

    let mut second = package.sort("Expr", expr_type, vec![]);
    second.id = HostItemId::new(
        HostPackageKey::new("negative", "0.1.0", package.root()).unwrap(),
        ["negative", "other"],
        "OtherExpr",
        ItemKind::Sort,
        "",
    )
    .unwrap();
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-NEG")],
            [package.sort("Expr", expr_type, vec![]), second],
        ),
        CollectionErrorKind::DuplicateTypeDeclaration,
    );
}

#[test]
fn rejects_duplicate_contexts_namespaces_and_missing_type_declarations() {
    let package = TestPackage::new("contexts", "#[k::sort]\npub trait Expr {}\n");
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-ONE"), package.context("ORG-TWO")],
            [package.sort("Expr", expr_type, vec![])],
        ),
        CollectionErrorKind::DuplicatePackageContext,
    );

    let other = TestPackage::new("other_context", "#[k::sort]\npub trait Expr {}\n");
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-SAME"), other.context("ORG-SAME")],
            std::iter::empty(),
        ),
        CollectionErrorKind::DuplicateKNamespace,
    );

    let mut missing_type = package.sort("Expr", expr_type, vec![]);
    missing_type.declared_type = None;
    assert_kind(
        collect_host_descriptors([package.context("ORG-MISSING")], [missing_type]),
        CollectionErrorKind::MissingTypeDeclaration,
    );
}

#[test]
fn rejects_unresolved_wrong_kind_and_duplicate_rule_reference_keys() {
    let package = TestPackage::new(
        "references",
        r"#[k::sort]
pub trait Expr {}
#[k::constructor(sort = Expr)]
pub struct Foo;
#[k::rule]
fn step(Foo(value): Term<dyn Expr>) -> Term<dyn Expr> { term!(Foo(value)) }
",
    );
    let constructor = package.constructor("Foo", foo_type, expr_type);
    assert_kind(
        collect_host_descriptors([package.context("ORG-REF")], [constructor.clone()]),
        CollectionErrorKind::UnresolvedTypeReference,
    );

    let mut wrong = constructor;
    if let HostDescriptorPayload::Constructor(payload) = &mut wrong.payload {
        payload.sort.target = type_ref(foo_type, "Foo");
    }
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-REF")],
            [package.sort("Expr", expr_type, vec![]), wrong],
        ),
        CollectionErrorKind::ReferenceKindMismatch,
    );

    let mut rule = package.rule("step", expr_type, foo_type);
    if let HostDescriptorPayload::Rule(payload) = &mut rule.payload {
        payload.references.push(payload.references[0].clone());
    }
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-REF")],
            [
                package.sort("Expr", expr_type, vec![]),
                package.constructor("Foo", foo_type, expr_type),
                rule,
            ],
        ),
        CollectionErrorKind::InvalidReferenceKey,
    );

    let mut invalid_bindings = package.rule("step", expr_type, foo_type);
    if let HostDescriptorPayload::Rule(payload) = &mut invalid_bindings.payload {
        payload.parameters[0].bindings = vec!["value".into(), "value".into()];
    }
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-REF")],
            [
                package.sort("Expr", expr_type, vec![]),
                package.constructor("Foo", foo_type, expr_type),
                invalid_bindings,
            ],
        ),
        CollectionErrorKind::InvalidRuleBindings,
    );
}

#[test]
fn rejects_wrong_display_out_of_bounds_and_imprecise_anchors() {
    let package = TestPackage::new("anchors", "#[k::sort]\npub trait Expr {}\n");
    let mut wrong_file = package.sort("Expr", expr_type, vec![]);
    wrong_file.provenance = replace_display(&wrong_file.provenance, "src/missing.rs");
    assert_kind(
        collect_host_descriptors([package.context("ORG-ANCHOR")], [wrong_file]),
        CollectionErrorKind::HostIo,
    );

    let mut out_of_bounds = package.sort("Expr", expr_type, vec![]);
    out_of_bounds.provenance = replace_first_anchor(
        &out_of_bounds.provenance,
        &HostSourceAnchor::new(
            "src/lib.rs",
            HostSourcePosition::new(99, 1).unwrap(),
            HostSourcePosition::new(99, 2).unwrap(),
            AnchorPrecision::Exact,
        )
        .unwrap(),
    );
    assert_kind(
        collect_host_descriptors([package.context("ORG-ANCHOR")], [out_of_bounds]),
        CollectionErrorKind::SourcePositionOutOfBounds,
    );

    let mut imprecise = package.sort("Expr", expr_type, vec![]);
    let original = imprecise.provenance.authored()[0].anchor();
    let fallback = HostSourceAnchor::new(
        original.display_file(),
        original.start(),
        original.end(),
        AnchorPrecision::InvocationFallback,
    )
    .unwrap();
    imprecise.provenance = replace_first_anchor(&imprecise.provenance, &fallback);
    assert_kind(
        collect_host_descriptors([package.context("ORG-ANCHOR")], [imprecise]),
        CollectionErrorKind::ImpreciseAuthoredAnchor,
    );
}

#[cfg(unix)]
#[test]
fn source_symlinks_cannot_escape_the_canonical_package_directory() {
    let package = TestPackage::new("escape", "#[k::sort]\npub trait Expr {}\n");
    let external = TestDirectory::new("external-source");
    let external_source = external.path.join("outside.rs");
    fs::write(&external_source, "#[k::sort]\npub trait Expr {}\n").unwrap();
    std::os::unix::fs::symlink(&external_source, package.root().join("src/escape.rs")).unwrap();
    let mut descriptor = package.sort("Expr", expr_type, vec![]);
    descriptor.provenance = replace_display(&descriptor.provenance, "src/escape.rs");
    assert_kind(
        collect_host_descriptors([package.context("ORG-ESCAPE")], [descriptor]),
        CollectionErrorKind::SourceOutsidePackage,
    );
}

#[test]
fn workspace_relative_display_hint_produces_the_package_relative_bundle() {
    let package = TestPackage::new_nested(
        "workspace_hint",
        "workspace/layers/packages/workspace_hint",
        "#[k::sort]\npub trait Expr {}\n",
    );
    let package_descriptor = package.sort("Expr", expr_type, vec![]);
    let package_bundle = collect_host_descriptors(
        [package.context("ORG-WORKSPACE-HINT")],
        [package_descriptor.clone()],
    )
    .unwrap();
    let workspace_hint = package
        .root()
        .strip_prefix(&package.directory.path)
        .unwrap()
        .join("src/lib.rs")
        .to_string_lossy()
        .replace('\\', "/");
    let mut workspace_descriptor = package_descriptor;
    workspace_descriptor.provenance =
        replace_display(&workspace_descriptor.provenance, &workspace_hint);
    let workspace_bundle = collect_host_descriptors(
        [package.context("ORG-WORKSPACE-HINT")],
        [workspace_descriptor],
    )
    .unwrap();

    assert_eq!(package_bundle, workspace_bundle);
    let krs_ir::OriginFrame::Ranged { range, .. } =
        &workspace_bundle.descriptors[0].origin().frames()[0]
    else {
        panic!("first frame must be authored")
    };
    assert_eq!(range.file.package_relative_path(), "src/lib.rs");
}

#[cfg(unix)]
#[test]
fn canonical_source_candidates_are_deduplicated_across_symlinks() {
    let package = TestPackage::new("source_alias", "#[k::sort]\npub trait Expr {}\n");
    let package_component = package.root().file_name().unwrap().to_string_lossy();
    std::os::unix::fs::symlink(
        package.root(),
        package.root().join(package_component.as_ref()),
    )
    .unwrap();
    let display_hint = format!("{package_component}/src/lib.rs");
    let mut descriptor = package.sort("Expr", expr_type, vec![]);
    descriptor.provenance = replace_display(&descriptor.provenance, &display_hint);
    let bundle = collect_host_descriptors([package.context("ORG-ALIAS")], [descriptor]).unwrap();
    let krs_ir::OriginFrame::Ranged { range, .. } = &bundle.descriptors[0].origin().frames()[0]
    else {
        panic!("first frame must be authored")
    };
    assert_eq!(range.file.package_relative_path(), "src/lib.rs");
}

#[test]
fn multiple_distinct_in_package_source_candidates_are_rejected() {
    let package = TestPackage::new("source_ambiguity", "#[k::sort]\npub trait Expr {}\n");
    let package_component = package.root().file_name().unwrap().to_string_lossy();
    let nested = package.root().join(package_component.as_ref()).join("src");
    fs::create_dir_all(&nested).unwrap();
    fs::write(nested.join("lib.rs"), "#[k::sort]\npub trait Expr {}\n").unwrap();
    let display_hint = format!("{package_component}/src/lib.rs");
    let mut descriptor = package.sort("Expr", expr_type, vec![]);
    descriptor.provenance = replace_display(&descriptor.provenance, &display_hint);
    assert_kind(
        collect_host_descriptors([package.context("ORG-SOURCE-AMBIGUITY")], [descriptor]),
        CollectionErrorKind::AmbiguousSourcePath,
    );
}

#[test]
fn duplicate_reparsed_invocations_are_rejected_as_ambiguous() {
    let package = TestPackage::new(
        "ambiguous",
        "#[k::sort]\n#[another::sort]\npub trait Expr {}\n",
    );
    assert_kind(
        collect_host_descriptors(
            [package.context("ORG-AMBIGUOUS")],
            [package.sort("Expr", expr_type, vec![])],
        ),
        CollectionErrorKind::AmbiguousAnchor,
    );
}

#[test]
fn collection_rejects_block_comments_in_every_dsl_body_at_exact_bytes() {
    let cases = [
        (
            "dsl_block_rules",
            r"#[k::sort]
pub trait Expr {}
k::rules! {
    for Expr;
    use Op::*;
    eval: Neg { value } /*krs-f7-block*/ => value;
}
",
            "rules!",
        ),
        (
            "dsl_block_cells",
            r"#[k::sort]
pub trait Expr {}
fn fixture() {
    let _ = cells! { k: KCell(value /*krs-f7-block*/, ..tail), ..state };
}
",
            "cells!",
        ),
        (
            "dsl_block_map",
            r"#[k::sort]
pub trait Expr {}
fn fixture() {
    let _ = map! { name /*krs-f7-block*/ -> value, rest @ .. };
}
",
            "map!",
        ),
    ];
    for (name, source, diagnostic_macro) in cases {
        let package = TestPackage::new(name, source);
        let error = collect_host_descriptors(
            [package.context("KRS-F7-COLLECTOR")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::SourceSyntax);
        let start = source.find("/*krs-f7-block*/").unwrap();
        let end = start + "/*krs-f7-block*/".len();
        assert!(
            error.detail().contains(&format!("bytes {start}..{end}")),
            "{}",
            error.detail()
        );
        assert!(error.detail().contains(diagnostic_macro), "{error}");
    }
}

#[test]
fn line_comment_dsl_reparse_preserves_identity_payload_topology_and_exact_anchors() {
    let baseline_source = r"#[k::sort]
pub trait Expr {}
";
    let commented_source = r"#[k::sort]
pub trait Expr {}
k::rules! {
    for Expr;
    use Op::*;
    // The comment is trivia, not rule payload.
    eval: Neg { value } => value;
}
fn fixture() {
    let _ = cells! {
        k: KCell(value, // preserve the continuation
            ..tail),
        ..state
    };
    let _ = map! {
        name -> value, // preserve the remainder
        rest @ ..
    };
}
";
    let baseline = TestPackage::new("dsl_line_comments", baseline_source);
    let commented = TestPackage::new("dsl_line_comments", commented_source);
    let baseline_bundle = collect_host_descriptors(
        [baseline.context("KRS-F7-COLLECTOR")],
        [baseline.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    let commented_bundle = collect_host_descriptors(
        [commented.context("KRS-F7-COLLECTOR")],
        [commented.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    let baseline_descriptor = &baseline_bundle.descriptors[0];
    let commented_descriptor = &commented_bundle.descriptors[0];
    assert_eq!(baseline_descriptor.id, commented_descriptor.id);
    assert_eq!(baseline_descriptor.payload, commented_descriptor.payload);
    let topology = |descriptor: &krs_ir::Descriptor| {
        descriptor
            .provenance
            .origins()
            .iter()
            .map(|origin| origin.key.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(
        topology(baseline_descriptor),
        topology(commented_descriptor)
    );
    let authored_range = |descriptor: &krs_ir::Descriptor| {
        let krs_ir::OriginFrame::Ranged { range, .. } = &descriptor.origin().frames()[0] else {
            panic!("the primary frame must remain authored")
        };
        (range.start_byte, range.end_byte)
    };
    assert_eq!(
        authored_range(baseline_descriptor),
        authored_range(commented_descriptor)
    );
    let (start, end) = authored_range(commented_descriptor);
    assert_eq!(&commented_source[start as usize..end as usize], "Expr");
}

#[test]
fn zero_and_multiple_rule_bindings_are_preserved_without_synthesis() {
    let package = TestPackage::new(
        "bindings",
        r"#[k::sort]
pub trait Expr {}
#[k::constructor(sort = Expr)]
pub struct Foo;
#[k::rule]
fn pair(Foo(left, right): Term<dyn Expr>) -> Term<dyn Expr> { term!(Foo(left)) }
#[k::rule]
fn unit(Foo: Term<dyn Expr>) -> Term<dyn Expr> { term!(Foo) }
",
    );
    let bundle = collect_host_descriptors(
        [package.context("ORG-BINDINGS")],
        [
            package.sort("Expr", expr_type, vec![]),
            package.constructor("Foo", foo_type, expr_type),
            package.rule("pair", expr_type, foo_type),
            package.rule("unit", expr_type, foo_type),
        ],
    )
    .unwrap();
    let mut binding_lists = bundle
        .descriptors
        .iter()
        .filter_map(|descriptor| match &descriptor.payload {
            krs_ir::DescriptorPayload::Rule(rule) => Some(rule.parameters[0].bindings.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    binding_lists.sort();
    assert_eq!(binding_lists, [vec![], vec!["left", "right"]]);
}

#[test]
fn split_configuration_and_initializer_files_merge_exact_v5_provenance() {
    let configuration_source = r#"#[k::sort]
pub trait KItem {}
#[k::constructor(sort = KItem, syntax = "foo")]
pub struct Foo;
#[k::configuration(root = "machine")]
pub struct Machine { pub k: k::configuration::KCell<k::builtin::KSequence> }
"#;
    let initializer_source = r"impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::configuration::KCell::new(k![Foo]) }
    }
}
";
    let package = TestPackage::new("split_configuration", configuration_source);
    fs::write(
        package.root().join("src/initializer.rs"),
        initializer_source,
    )
    .unwrap();
    let configuration = package.configuration(
        configuration_source,
        initializer_source,
        "src/initializer.rs",
        foo_type,
    );
    let bundle = collect_host_descriptors(
        [package.context("KRS-M2-REFERENCE")],
        [
            package.sort("KItem", kitem_type, vec![]),
            package.constructor("Foo", foo_type, kitem_type),
            configuration,
        ],
    )
    .unwrap();
    let descriptor = bundle
        .descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
        .unwrap();
    assert_eq!(descriptor.provenance.origins().len(), 15);
    let declaration = descriptor
        .provenance
        .origin_for(&ProvenanceRole::ConfigurationDeclaration.key(0).unwrap())
        .unwrap();
    let initializer = descriptor
        .provenance
        .origin_for(&ProvenanceRole::InitializerDeclaration.key(0).unwrap())
        .unwrap();
    let term_path = descriptor
        .provenance
        .origin_for(&ProvenanceRole::InitializerTermPath.key(0).unwrap())
        .unwrap();
    let file = |origin: &krs_ir::OriginStack| match &origin.frames()[0] {
        krs_ir::OriginFrame::Ranged { range, .. } => range.file.package_relative_path().to_owned(),
        krs_ir::OriginFrame::Transformation { .. } => {
            panic!("first frame must be authored")
        }
    };
    assert_eq!(file(declaration), "src/lib.rs");
    assert_eq!(file(initializer), "src/initializer.rs");
    assert_eq!(file(term_path), "src/initializer.rs");
    let json = bundle.to_canonical_json().unwrap();
    assert!(!json.contains(package.root().to_str().unwrap()));
    assert!(!json.contains("KCell"));
    assert!(!json.contains("owner_type"));
}

#[test]
#[allow(clippy::too_many_lines)]
fn collected_m2_bundle_reaches_canonical_semantic_definition_and_k() {
    use krs_compiler::{emit_k, lower_descriptor_bundle, lower_semantic_theory};

    let source = r#"#[k::sort]
pub trait KItem {}
#[k::sort]
pub trait KResult: KItem {}
#[k::sort]
pub trait M2Obj: KResult {}
#[k::constructor(sort = M2Obj, syntax = "foo")]
pub struct Foo;
#[k::constructor(sort = M2Obj, syntax = "bar")]
pub struct Bar;
#[k::configuration(root = "machine")]
pub struct Machine { pub k: k::configuration::KCell<k::builtin::KSequence> }
#[k::rule]
fn foo_to_bar(Foo: Term<dyn M2Obj>) -> Term<dyn M2Obj> { term!(Bar) }
"#;
    let initializer = r"impl Machine {
    #[k::init]
    pub fn init() -> Self {
        Self { k: k::configuration::KCell::new(k![Foo]) }
    }
}
";
    let package = TestPackage::new("m2_semantics", source);
    fs::write(package.root().join("src/initializer.rs"), initializer).unwrap();
    let descriptors = vec![
        package.sort("KItem", kitem_type, vec![]),
        package.sort("KResult", kresult_type, vec![type_ref(kitem_type, "KItem")]),
        package.sort("M2Obj", m2obj_type, vec![type_ref(kresult_type, "KResult")]),
        package.constructor("Foo", foo_type, m2obj_type),
        package.constructor("Bar", bar_type, m2obj_type),
        package.configuration(source, initializer, "src/initializer.rs", foo_type),
        package.transition("foo_to_bar", m2obj_type, foo_type, bar_type),
    ];
    let bundle =
        collect_host_descriptors([package.context("KRS-M2-REFERENCE")], descriptors.clone())
            .unwrap();
    let reordered = collect_host_descriptors(
        [package.context("KRS-M2-REFERENCE")],
        descriptors.into_iter().rev(),
    )
    .unwrap();
    assert_eq!(
        bundle.to_canonical_json().unwrap(),
        reordered.to_canonical_json().unwrap()
    );
    assert_eq!(bundle.protocol_version(), ProtocolVersion::CURRENT);

    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let reordered_semantic = lower_descriptor_bundle(&reordered).unwrap();
    assert_eq!(
        semantic.to_canonical_json().unwrap(),
        reordered_semantic.to_canonical_json().unwrap()
    );
    assert_eq!(semantic.schema_version().0, 27);
    let module = &semantic.modules()[0];
    let subsort_names = module
        .subsorts()
        .iter()
        .map(|edge| match (edge.subsort(), edge.supersort()) {
            (
                krs_ir::SemanticSortRef::Declared(subsort),
                krs_ir::SemanticSortRef::Declared(supersort),
            ) => (subsort.item_name(), supersort.item_name()),
            _ => panic!("M2 subsort endpoints must remain authored sorts"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        subsort_names,
        vec![("KResult", "KItem"), ("M2Obj", "KResult")]
    );
    let grammar_origins = module
        .productions()
        .iter()
        .flat_map(krs_ir::SemanticProduction::items)
        .map(|item| {
            assert!(matches!(
                item.origin().origin().frames().first(),
                Some(krs_ir::OriginFrame::Ranged { .. })
            ));
            item.origin().key().clone()
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(grammar_origins.len(), 2);
    assert!(
        module
            .productions()
            .iter()
            .all(|production| production.attributes().is_empty())
    );
    let lowered = lower_semantic_theory(&semantic).unwrap();
    let reordered_lowered = lower_semantic_theory(&reordered_semantic).unwrap();
    assert_eq!(lowered.definition().schema_version().0, 27);
    let shared_ir = format!(
        "{}{}",
        semantic.to_canonical_json().unwrap(),
        lowered.definition().to_canonical_json().unwrap()
    );
    for forbidden in ["native_id", "k_rust", "raw_attribute", "adapter_id"] {
        assert!(!shared_ir.contains(forbidden));
    }
    let initializer_leaf = bundle
        .descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
        .unwrap()
        .provenance
        .origin_for(&ProvenanceRole::InitializerTermPath.key(0).unwrap())
        .unwrap()
        .frames()[0]
        .clone();
    assert!(lowered.source_map().entries().iter().any(|entry| {
        entry.origin().frames().first() == Some(&initializer_leaf)
            && entry.origin().frames().iter().any(|frame| {
                matches!(
                    frame,
                    krs_ir::OriginFrame::Transformation {
                        kind: krs_ir::TransformationOriginKind::SemanticIr,
                        ..
                    }
                )
            })
            && entry.origin().frames().iter().any(|frame| {
                matches!(
                    frame,
                    krs_ir::OriginFrame::Transformation {
                        kind: krs_ir::TransformationOriginKind::DefinitionIr,
                        ..
                    }
                )
            })
    }));
    assert!(
        emit_k(&lowered)
            .unwrap()
            .source_map()
            .entries()
            .iter()
            .any(|entry| entry.origin().frames().first() == Some(&initializer_leaf))
    );
    assert_eq!(
        digest(&bundle.to_canonical_json().unwrap()),
        "3ce6f64c71edf54e4e7453359b8a27acc3c343f48582802588fb42325469af60"
    );
    assert_eq!(
        digest(&semantic.to_canonical_json().unwrap()),
        "3c4aff14e7d212f461db1c4a99335663ae0fff29fd4721e8721a66b76c8bb16f"
    );
    assert_eq!(
        digest(&lowered.definition().to_canonical_json().unwrap()),
        "70c37b5ef8aabcfe795885f5feed200a246ee25e750082561018690f903f3530"
    );
    assert_eq!(
        digest(&lowered.symbol_map().to_canonical_json().unwrap()),
        "b6d58a5bf91eae0744a0180091cc44be02aad9eecdcdeaca69c7de5739eae8d5"
    );
    assert_eq!(
        digest(&lowered.source_map().to_canonical_json().unwrap()),
        "3f0aa3f421e4054f6913fb89526ffe7e8c9c7f410343837dd939798fdae5563b"
    );
    assert_eq!(
        digest(emit_k(&lowered).unwrap().source()),
        "6fac1fbe096a70ef1bad795f8e2dcef6597c2b9d69219b633f8c430d1b7767d8"
    );
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        reordered_lowered.definition().to_canonical_json().unwrap()
    );
    assert_eq!(
        lowered.source_map().to_canonical_json().unwrap(),
        reordered_lowered.source_map().to_canonical_json().unwrap()
    );
    assert_eq!(
        lowered.symbol_map().to_canonical_json().unwrap(),
        reordered_lowered.symbol_map().to_canonical_json().unwrap()
    );
    assert_eq!(
        emit_k(&lowered).unwrap().source(),
        r#"module KRS-M2-REFERENCE
  syntax KItem
  syntax KResult
  syntax M2Obj

  syntax M2Obj ::= "bar" [symbol(bar)]
  syntax M2Obj ::= "foo" [symbol(foo)]

  syntax KItem ::= KResult
  syntax KResult ::= M2Obj

  configuration <k> foo </k>

  rule foo => bar [label(krsRule_2062992b8378c13e5a704d5c)]
endmodule
"#
    );

    let relocated = TestPackage::new("m2_semantics", source);
    fs::write(relocated.root().join("src/initializer.rs"), initializer).unwrap();
    let relocated_bundle = collect_host_descriptors(
        [relocated.context("KRS-M2-REFERENCE")],
        [
            relocated.sort("KItem", kitem_type, vec![]),
            relocated.sort("KResult", kresult_type, vec![type_ref(kitem_type, "KItem")]),
            relocated.sort("M2Obj", m2obj_type, vec![type_ref(kresult_type, "KResult")]),
            relocated.constructor("Foo", foo_type, m2obj_type),
            relocated.constructor("Bar", bar_type, m2obj_type),
            relocated.configuration(source, initializer, "src/initializer.rs", foo_type),
            relocated.transition("foo_to_bar", m2obj_type, foo_type, bar_type),
        ],
    )
    .unwrap();
    assert_eq!(
        bundle.to_canonical_json().unwrap(),
        relocated_bundle.to_canonical_json().unwrap()
    );
    let relocated_semantic = lower_descriptor_bundle(&relocated_bundle).unwrap();
    assert_eq!(
        semantic.to_canonical_json().unwrap(),
        relocated_semantic.to_canonical_json().unwrap()
    );
    assert_eq!(
        lowered.definition().to_canonical_json().unwrap(),
        lower_semantic_theory(&relocated_semantic)
            .unwrap()
            .definition()
            .to_canonical_json()
            .unwrap()
    );

    let mut missing_configuration = bundle.clone();
    missing_configuration
        .descriptors
        .retain(|descriptor| descriptor.id.item_kind() != ItemKind::Configuration);
    assert!(matches!(
        lower_descriptor_bundle(&missing_configuration),
        Err(krs_compiler::DescriptorLoweringError::ConfigurationCount(0))
    ));

    let mut duplicate_configuration = bundle.clone();
    let mut second = duplicate_configuration
        .descriptors
        .iter()
        .find(|descriptor| descriptor.id.item_kind() == ItemKind::Configuration)
        .unwrap()
        .clone();
    second.id = krs_ir::StableItemId::new(
        second.id.package().clone(),
        second.id.module_path().iter().cloned(),
        "OtherMachine",
        ItemKind::Configuration,
        "",
    )
    .unwrap();
    duplicate_configuration.descriptors.push(second);
    assert!(matches!(
        lower_descriptor_bundle(&duplicate_configuration),
        Err(krs_compiler::DescriptorLoweringError::ConfigurationCount(2))
    ));

    let mut missing_term_reference = bundle.clone();
    let configuration = missing_term_reference
        .descriptors
        .iter_mut()
        .find_map(|descriptor| match &mut descriptor.payload {
            krs_ir::DescriptorPayload::Configuration(configuration) => Some(configuration),
            _ => None,
        })
        .unwrap();
    configuration.initializer.references.clear();
    assert!(matches!(
        lower_descriptor_bundle(&missing_term_reference),
        Err(krs_compiler::DescriptorLoweringError::ParserReferenceDisagreement { .. })
    ));
}

fn digest(value: &str) -> String {
    format!("{:x}", Sha256::digest(value.as_bytes()))
}

#[test]
fn configuration_pairing_and_initializer_parser_disagreement_fail_typed() {
    let configuration_source = r#"#[k::sort]
pub trait KItem {}
#[k::constructor(sort = KItem)]
pub struct Foo;
#[k::configuration(root = "machine")]
pub struct Machine { pub k: KCell<KSequence> }
"#;
    let initializer_source =
        "impl Machine { #[k::init] fn init() -> Self { Self { k: KCell::new(k![Foo]) } } }";
    let package = TestPackage::new("configuration_negative", configuration_source);
    fs::write(
        package.root().join("src/initializer.rs"),
        initializer_source,
    )
    .unwrap();
    let base = package.configuration(
        configuration_source,
        initializer_source,
        "src/initializer.rs",
        foo_type,
    );
    let declarations = || {
        vec![
            package.sort("KItem", kitem_type, vec![]),
            package.constructor("Foo", foo_type, kitem_type),
        ]
    };

    let mut wrong_owner = base.clone();
    let HostDescriptorPayload::Configuration(configuration) = &mut wrong_owner.payload else {
        unreachable!()
    };
    configuration.initializer.owner_type = HostTypeKey(other_type);
    let mut descriptors = declarations();
    descriptors.push(wrong_owner);
    assert_kind(
        collect_host_descriptors([package.context("KRS-M2-NEGATIVE")], descriptors),
        CollectionErrorKind::InvalidConfiguration,
    );

    let mut wrong_term = base.clone();
    let HostDescriptorPayload::Configuration(configuration) = &mut wrong_term.payload else {
        unreachable!()
    };
    configuration.initializer.term = "Bar".into();
    let mut descriptors = declarations();
    descriptors.push(wrong_term);
    assert_kind(
        collect_host_descriptors([package.context("KRS-M2-NEGATIVE")], descriptors),
        CollectionErrorKind::ProvenanceMismatch,
    );

    let mut missing_reference = base;
    let HostDescriptorPayload::Configuration(configuration) = &mut missing_reference.payload else {
        unreachable!()
    };
    configuration.initializer.references.clear();
    let mut descriptors = declarations();
    descriptors.push(missing_reference);
    assert_kind(
        collect_host_descriptors([package.context("KRS-M2-NEGATIVE")], descriptors),
        CollectionErrorKind::ProvenanceMismatch,
    );
}

#[test]
fn optional_main_configuration_variable_lowers_as_a_bound_sequence_item() {
    use krs_compiler::lower_descriptor_bundle;

    let configuration_source = r#"#[k::sort]
pub trait KItem {}
#[k::constructor(sort = KItem)]
pub struct Foo;
#[k::configuration(root = "machine")]
pub struct Machine { pub k: KCell<KSequence> }
"#;
    let initializer_source = "impl Machine { #[k::init] fn init(\
        #[k::config_var(name = \"PGM\", main)] program: k::Term<dyn KItem>\
        ) -> Self { Self { k: KCell::new(k![program]) } } }";
    let package = TestPackage::new("configuration_variable", configuration_source);
    fs::write(
        package.root().join("src/initializer.rs"),
        initializer_source,
    )
    .unwrap();
    let mut configuration = package.configuration(
        configuration_source,
        initializer_source,
        "src/initializer.rs",
        foo_type,
    );
    let HostDescriptorPayload::Configuration(payload) = &mut configuration.payload else {
        unreachable!()
    };
    payload.main_variable = Some(HostConfigurationVariableDescriptor {
        binding: "program".into(),
        external_name: "PGM".into(),
        sort: HostDescriptorReference::new(
            ProvenanceRole::ConfigurationVariableType.key(0).unwrap(),
            type_ref(kitem_type, "KItem"),
        ),
    });
    payload.initializer.references.clear();
    let bundle = collect_host_descriptors(
        [package.context("KRS-M2-VARIABLE")],
        [
            package.sort("KItem", kitem_type, vec![]),
            package.constructor("Foo", foo_type, kitem_type),
            configuration,
        ],
    )
    .unwrap();
    let semantic = lower_descriptor_bundle(&bundle).unwrap();
    let initializer = semantic.modules()[0]
        .configuration()
        .unwrap()
        .initializer()
        .unwrap();
    assert_eq!(initializer.variables().len(), 1);
    assert_eq!(initializer.variables()[0].id().as_str(), "PGM");
    assert!(matches!(
        initializer.body().kind(),
        krs_ir::SemanticTermKind::KSequence { items, .. }
            if matches!(items[0].kind(), krs_ir::SemanticTermKind::Variable { variable } if variable.as_str() == "PGM")
    ));
}

fn assert_kind(
    result: Result<krs_ir::DescriptorBundle, krs_compiler::CollectionError>,
    expected: CollectionErrorKind,
) {
    assert_eq!(result.unwrap_err().kind(), expected);
}

fn type_ref(key: fn() -> TypeId, path: &str) -> HostTypeReference {
    HostTypeReference {
        key: HostTypeKey(key),
        authored_path: path.into(),
    }
}

fn replace_display(provenance: &HostProvenance, display: &str) -> HostProvenance {
    let authored = provenance
        .authored()
        .iter()
        .map(|item| {
            let old = item.anchor();
            HostAuthoredAnchor::new(
                item.key().clone(),
                HostSourceAnchor::new(display, old.start(), old.end(), old.precision()).unwrap(),
            )
        })
        .collect();
    let old = provenance.invocation();
    HostProvenance::new(
        HostSourceAnchor::new(display, old.start(), old.end(), old.precision()).unwrap(),
        authored,
    )
    .unwrap()
}

fn replace_first_anchor(
    provenance: &HostProvenance,
    replacement: &HostSourceAnchor,
) -> HostProvenance {
    let authored = provenance
        .authored()
        .iter()
        .enumerate()
        .map(|(index, item)| {
            HostAuthoredAnchor::new(
                item.key().clone(),
                if index == 0 {
                    replacement.clone()
                } else {
                    item.anchor().clone()
                },
            )
        })
        .collect();
    HostProvenance::new(provenance.invocation().clone(), authored).unwrap()
}

#[derive(Debug)]
struct TestPackage {
    directory: TestDirectory,
    package_root: PathBuf,
    name: String,
    source: String,
}

impl TestPackage {
    fn new(name: &str, source: &str) -> Self {
        Self::new_nested(name, "", source)
    }

    fn new_nested(name: &str, relative_root: &str, source: &str) -> Self {
        let directory = TestDirectory::new(name);
        let package_root = directory.path.join(relative_root);
        fs::create_dir_all(package_root.join("src")).unwrap();
        fs::write(
            package_root.join("Cargo.toml"),
            format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\n"),
        )
        .unwrap();
        fs::write(package_root.join("src/lib.rs"), source).unwrap();
        Self {
            directory,
            package_root,
            name: name.into(),
            source: source.into(),
        }
    }

    fn root(&self) -> &Path {
        &self.package_root
    }

    fn context(&self, namespace: &str) -> PackageContext {
        PackageContext::new(
            namespace,
            &self.name,
            "0.1.0",
            "workspace",
            &self.name,
            self.root().join("Cargo.toml"),
        )
        .unwrap()
    }

    fn item_id(&self, name: &str, kind: ItemKind, module: &[&str]) -> HostItemId {
        let package = HostPackageKey::new(&self.name, "0.1.0", self.root()).unwrap();
        let mut path = vec![self.name.as_str()];
        path.extend_from_slice(module);
        HostItemId::new(package, path, name, kind, "").unwrap()
    }

    fn sort(
        &self,
        name: &str,
        declared: fn() -> TypeId,
        parents: Vec<HostTypeReference>,
    ) -> HostDescriptor {
        self.sort_in_module_with_parents(name, 0, "", declared, parents)
    }

    fn sort_in_module(
        &self,
        name: &str,
        occurrence: usize,
        module: &str,
        declared: fn() -> TypeId,
    ) -> HostDescriptor {
        self.sort_in_module_with_parents(name, occurrence, module, declared, vec![])
    }

    fn sort_in_module_with_parents(
        &self,
        name: &str,
        occurrence: usize,
        module: &str,
        declared: fn() -> TypeId,
        parents: Vec<HostTypeReference>,
    ) -> HostDescriptor {
        let trait_item = find_traits(&syn::parse_file(&self.source).unwrap().items)
            .into_iter()
            .filter(|item| item.ident == name)
            .nth(occurrence)
            .unwrap();
        let symbol = trait_item
            .attrs
            .iter()
            .find(|attribute| attribute_named(attribute, "symbol"))
            .map(|attribute| parse_symbol_attribute(attribute_tokens(attribute)).unwrap());
        let mut anchors = SortDeclaration::from_item(trait_item)
            .unwrap()
            .provenance()
            .unwrap();
        if let Some(symbol) = symbol {
            anchors.extend(symbol.provenance().unwrap());
        }
        let module_path = if module.is_empty() {
            Vec::new()
        } else {
            vec![module]
        };
        HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id: self.item_id(name, ItemKind::Sort, &module_path),
            declared_type: Some(krs_ir::HostDeclarationIdentity::Nominal(HostTypeKey(
                declared,
            ))),
            payload: HostDescriptorPayload::Sort(HostSortDescriptor { parents }),
            cfg: BTreeMap::new(),
            provenance: host_provenance("src/lib.rs", anchors),
        }
    }

    fn constructor(
        &self,
        name: &str,
        declared: fn() -> TypeId,
        sort: fn() -> TypeId,
    ) -> HostDescriptor {
        let source = syn::parse_file(&self.source).unwrap();
        let item = source
            .items
            .iter()
            .find_map(|item| match item {
                Item::Struct(item) if item.ident == name => Some(item),
                _ => None,
            })
            .unwrap();
        let attribute = item
            .attrs
            .iter()
            .find(|attribute| attribute.path().segments.last().unwrap().ident == "constructor")
            .unwrap();
        let Meta::List(list) = &attribute.meta else {
            panic!("constructor attribute must be a list")
        };
        let parsed = parse_constructor_attribute(list.tokens.clone()).unwrap();
        let declaration = ConstructorDeclaration::from_item(item.clone()).unwrap();
        let mut provenance = parsed.provenance().unwrap();
        provenance.extend(declaration.provenance().unwrap());
        if let Some(symbol) = item
            .attrs
            .iter()
            .find(|attribute| attribute_named(attribute, "symbol"))
        {
            provenance.extend(
                parse_symbol_attribute(attribute_tokens(symbol))
                    .unwrap()
                    .provenance()
                    .unwrap(),
            );
        }
        let fields = match &item.fields {
            syn::Fields::Named(fields) => fields
                .named
                .iter()
                .map(|field| HostConstructorFieldDescriptor {
                    name: field.ident.as_ref().unwrap().to_string(),
                    sort: type_ref(sort, "Expr"),
                })
                .collect(),
            syn::Fields::Unnamed(_) | syn::Fields::Unit => Vec::new(),
        };
        HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id: self.item_id(name, ItemKind::Constructor, &[]),
            declared_type: Some(krs_ir::HostDeclarationIdentity::Nominal(HostTypeKey(
                declared,
            ))),
            payload: HostDescriptorPayload::Constructor(HostConstructorDescriptor {
                sort: krs_ir::HostSortReference {
                    key: krs_ir::ProvenanceKey::new("constructor_sort", 0).unwrap(),
                    target: type_ref(sort, "Expr"),
                },
                syntax: parsed.syntax.as_ref().map(syn::LitStr::value),
                fields,
            }),
            cfg: BTreeMap::new(),
            provenance: host_provenance("src/lib.rs", provenance),
        }
    }

    fn rule(
        &self,
        name: &str,
        sort: fn() -> TypeId,
        constructor: fn() -> TypeId,
    ) -> HostDescriptor {
        let source = syn::parse_file(&self.source).unwrap();
        let item = source
            .items
            .iter()
            .find_map(|item| match item {
                Item::Fn(item) if item.sig.ident == name => Some(item.clone()),
                _ => None,
            })
            .unwrap();
        let parsed = RuleItem::from_item(item).unwrap();
        let bindings = parsed
            .parameter()
            .pattern
            .bindings()
            .iter()
            .map(ToString::to_string)
            .collect();
        HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id: self.item_id(name, ItemKind::Rule, &[]),
            declared_type: None,
            payload: HostDescriptorPayload::Rule(HostRuleDescriptor {
                sentence_kind: SentenceKind::Transition,
                parameters: vec![HostRuleParameterDescriptor {
                    bindings,
                    sort: type_ref(sort, "Expr"),
                    pattern: parsed.parameter().pattern.spelling(),
                }],
                result_sort: type_ref(sort, "Expr"),
                references: vec![
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleType.key(0).unwrap(),
                        type_ref(sort, "Expr"),
                    ),
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleResultType.key(0).unwrap(),
                        type_ref(sort, "Expr"),
                    ),
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleLeftPath.key(0).unwrap(),
                        type_ref(constructor, "Foo"),
                    ),
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleRightPath.key(0).unwrap(),
                        type_ref(constructor, "Foo"),
                    ),
                ],
                lhs: parsed.parameter().pattern.spelling(),
                rhs: parsed.result().spelling(),
            }),
            cfg: BTreeMap::new(),
            provenance: host_provenance("src/lib.rs", parsed.provenance().unwrap()),
        }
    }

    fn transition(
        &self,
        name: &str,
        sort: fn() -> TypeId,
        left: fn() -> TypeId,
        right: fn() -> TypeId,
    ) -> HostDescriptor {
        let source = syn::parse_file(&self.source).unwrap();
        let item = source
            .items
            .iter()
            .find_map(|item| match item {
                Item::Fn(item) if item.sig.ident == name => Some(item.clone()),
                _ => None,
            })
            .unwrap();
        let parsed = RuleItem::from_item(item).unwrap();
        HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id: self.item_id(name, ItemKind::Rule, &[]),
            declared_type: None,
            payload: HostDescriptorPayload::Rule(HostRuleDescriptor {
                sentence_kind: SentenceKind::Transition,
                parameters: vec![HostRuleParameterDescriptor {
                    bindings: Vec::new(),
                    sort: type_ref(sort, "M2Obj"),
                    pattern: parsed.parameter().pattern.spelling(),
                }],
                result_sort: type_ref(sort, "M2Obj"),
                references: vec![
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleType.key(0).unwrap(),
                        type_ref(sort, "M2Obj"),
                    ),
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleResultType.key(0).unwrap(),
                        type_ref(sort, "M2Obj"),
                    ),
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleLeftPath.key(0).unwrap(),
                        type_ref(left, "Foo"),
                    ),
                    HostDescriptorReference::new(
                        ProvenanceRole::RuleRightPath.key(0).unwrap(),
                        type_ref(right, "Bar"),
                    ),
                ],
                lhs: parsed.parameter().pattern.spelling(),
                rhs: parsed.result().spelling(),
            }),
            cfg: BTreeMap::new(),
            provenance: host_provenance("src/lib.rs", parsed.provenance().unwrap()),
        }
    }

    fn configuration(
        &self,
        configuration_source: &str,
        initializer_source: &str,
        initializer_display: &str,
        initializer_constructor: fn() -> TypeId,
    ) -> HostDescriptor {
        let configuration_file = syn::parse_file(configuration_source).unwrap();
        let item = configuration_file
            .items
            .iter()
            .find_map(|item| match item {
                Item::Struct(item) if item.ident == "Machine" => Some(item.clone()),
                _ => None,
            })
            .unwrap();
        let attribute = item
            .attrs
            .iter()
            .find(|attribute| attribute.path().segments.last().unwrap().ident == "configuration")
            .unwrap();
        let Meta::List(list) = &attribute.meta else {
            panic!("configuration attribute must be a list")
        };
        let parsed_attribute = parse_configuration_attribute(list.tokens.clone()).unwrap();
        let declaration = ConfigurationDeclaration::from_item(item).unwrap();
        let mut configuration_anchors = parsed_attribute.provenance().unwrap();
        configuration_anchors.extend(declaration.provenance().unwrap());

        let initializer_file = syn::parse_file(initializer_source).unwrap();
        let mut method = initializer_file
            .items
            .iter()
            .find_map(|item| match item {
                Item::Impl(item) => item.items.iter().find_map(|item| match item {
                    ImplItem::Fn(method) if method.sig.ident == "init" => Some(method.clone()),
                    _ => None,
                }),
                _ => None,
            })
            .unwrap();
        method
            .attrs
            .retain(|attribute| attribute.path().segments.last().unwrap().ident != "init");
        let initializer = InitializerFunction::from_item(method).unwrap();
        HostDescriptor {
            protocol_version: ProtocolVersion::CURRENT,
            id: self.item_id("Machine", ItemKind::Configuration, &[]),
            declared_type: Some(krs_ir::HostDeclarationIdentity::Nominal(HostTypeKey(
                machine_type,
            ))),
            payload: HostDescriptorPayload::Configuration(HostConfigurationDescriptor {
                root: parsed_attribute.root().value(),
                cell: ConfigurationCellDescriptor {
                    name: declaration.cell().name().to_string(),
                    content_sort: BuiltinSort::KSequence,
                },
                main_variable: None,
                initializer: HostConfigurationInitializerDescriptor {
                    name: initializer.item().sig.ident.to_string(),
                    owner_type: HostTypeKey(machine_type),
                    provenance: host_provenance(
                        initializer_display,
                        initializer.provenance().unwrap(),
                    ),
                    term: initializer.cell().term().spelling(),
                    references: vec![HostDescriptorReference::new(
                        ProvenanceRole::InitializerTermPath.key(0).unwrap(),
                        type_ref(initializer_constructor, "Foo"),
                    )],
                },
            }),
            cfg: BTreeMap::new(),
            provenance: host_provenance("src/lib.rs", configuration_anchors),
        }
    }
}

fn find_traits(items: &[Item]) -> Vec<syn::ItemTrait> {
    let mut output = Vec::new();
    for item in items {
        match item {
            Item::Trait(item) => output.push(item.clone()),
            Item::Mod(module) => {
                if let Some((_, nested)) = &module.content {
                    output.extend(find_traits(nested));
                }
            }
            _ => {}
        }
    }
    output
}

fn host_provenance(display: &str, anchors: Vec<ProvenanceAnchor>) -> HostProvenance {
    let authored = anchors
        .into_iter()
        .map(|anchor| {
            HostAuthoredAnchor::new(
                anchor.key().unwrap(),
                source_anchor(display, anchor.range(), AnchorPrecision::Exact),
            )
        })
        .collect::<Vec<_>>();
    HostProvenance::new(authored[0].anchor().clone(), authored).unwrap()
}

fn source_anchor(
    display: &str,
    range: krs_syntax::TokenRange,
    precision: AnchorPrecision,
) -> HostSourceAnchor {
    let start = range.start();
    let end = range.end();
    let start_line = u32::try_from(start.line).unwrap();
    let start_column = u32::try_from(start.column).unwrap() + 1;
    let end_line = u32::try_from(end.line).unwrap();
    let end_column = u32::try_from(end.column).unwrap() + 1;
    HostSourceAnchor::new(
        display,
        HostSourcePosition::new(start_line, start_column).unwrap(),
        HostSourcePosition::new(end_line, end_column).unwrap(),
        precision,
    )
    .unwrap()
}

#[derive(Debug)]
struct TestDirectory {
    path: PathBuf,
}

impl TestDirectory {
    fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let sequence = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "krs-compiler-{label}-{}-{sequence}",
            std::process::id()
        ));
        if path.exists() {
            fs::remove_dir_all(&path).unwrap();
        }
        fs::create_dir(&path).unwrap();
        Self { path }
    }
}

impl Drop for TestDirectory {
    fn drop(&mut self) {
        if self.path.exists() {
            fs::remove_dir_all(&self.path).unwrap();
        }
    }
}
