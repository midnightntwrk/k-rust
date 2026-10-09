//! Host collection integration tests.

use krs_syntax::KrsSyntax;
use std::any::TypeId;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use krs_collector::{
    CollectionError, CollectionErrorKind, PackageContext, collect_host_descriptors,
};
use krs_ir::testing::assert_canonical_contract;
use krs_ir::{
    AnchorPrecision, HostAuthoredAnchor, HostConstructorDescriptor, HostConstructorFieldDescriptor,
    HostDescriptor, HostDescriptorPayload, HostItemId, HostPackageKey, HostProvenance,
    HostProvenanceError, HostSortDescriptor, HostSourceAnchor, HostSourcePosition, HostTypeKey,
    HostTypeReference, ItemKind, Position, ProvenanceRole, RustVisibility, SchemaVersion,
};
use krs_syntax::surface;
use krs_syntax::{ConstructorDeclaration, ProvenanceAnchor, SortDeclaration};
use krs_test_support::{TempDir, temp_dir};
use syn::{Item, Meta};

fn collect_descriptors(
    contexts: impl IntoIterator<Item = PackageContext>,
    descriptors: impl IntoIterator<Item = HostDescriptor>,
) -> Result<krs_ir::DescriptorBundle, CollectionError> {
    collect_host_descriptors(contexts, descriptors.into_iter().map(Ok))
}

fn is_symbol_attribute(attribute: &syn::Attribute) -> bool {
    surface::resolve(attribute.path(), "k")
        == Some(surface::Entry::Attribute(surface::AttributeMacro::Symbol))
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
struct OtherType;

fn kitem_type() -> TypeId {
    TypeId::of::<KItemType>()
}

fn expr_type() -> TypeId {
    TypeId::of::<ExprType>()
}

fn foo_type() -> TypeId {
    TypeId::of::<FooType>()
}

fn other_type() -> TypeId {
    TypeId::of::<OtherType>()
}

#[test]
fn collection_is_deterministic_and_resolves_sort_and_constructor_references() {
    let package = TestPackage::new(
        "semantics",
        r#"#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait Expr: KItem {}

#[k::constructor(sort = Expr, syntax = "foo({value})")]
pub struct Foo { pub value: Term<dyn Expr> }
"#,
    );
    let descriptors = vec![
        package.sort("KItem", kitem_type, vec![]),
        package.sort("Expr", expr_type, vec![type_ref(kitem_type, "KItem")]),
        package.constructor("Foo", foo_type, expr_type),
    ];

    let first =
        collect_descriptors([package.context("ORG-SEMANTICS")], descriptors.clone()).unwrap();
    assert_canonical_contract(&first);
    let second = collect_descriptors(
        [package.context("ORG-SEMANTICS")],
        descriptors.into_iter().rev(),
    )
    .unwrap();
    assert_canonical_contract(&second);

    assert_eq!(first, second);
    assert_eq!(first.descriptors().len(), 3);
    let json = first.to_canonical_json().unwrap();
    assert!(!json.contains(package.root().to_str().unwrap()));
    assert!(json.contains("constructor_sort"));
    assert!(json.contains("content_sha256"));
}

#[test]
fn intake_reports_the_same_first_error_in_either_registration_order() {
    let package = TestPackage::new(
        "intake_order",
        "#[k::sort]\npub trait Alpha {}\n#[k::sort]\npub trait Beta {}\n",
    );
    let mut alpha = package.sort("Alpha", expr_type, vec![]);
    alpha.protocol_version = SchemaVersion(100);
    let mut beta = package.sort("Beta", foo_type, vec![]);
    beta.protocol_version = SchemaVersion(200);

    let forward = collect_descriptors(
        [package.context("ORG-INTAKE")],
        [alpha.clone(), beta.clone()],
    )
    .unwrap_err();
    let reverse = collect_descriptors([package.context("ORG-INTAKE")], [beta, alpha]).unwrap_err();

    assert_eq!(forward, reverse);
    assert_eq!(
        forward.kind(),
        CollectionErrorKind::UnsupportedSchemaVersion
    );
    assert!(forward.detail().contains("schema 100"), "{forward}");
}

#[test]
fn factory_failures_report_the_same_unlocated_error_in_either_registration_order() {
    let first = HostProvenanceError {
        invocation_file: "src/lib.rs".to_owned(),
        invocation_start: HostSourcePosition::new(3, 7).unwrap(),
        display_file: "/target/build/semantics/out/generated.rs".to_owned(),
        manifest_dir: "/workspace/semantics".to_owned(),
        path_error: None,
    };
    let second = HostProvenanceError {
        invocation_file: "src/lib.rs".to_owned(),
        invocation_start: HostSourcePosition::new(5, 1).unwrap(),
        display_file: "/target/build/semantics/out/another.rs".to_owned(),
        manifest_dir: "/workspace/semantics".to_owned(),
        path_error: None,
    };
    let forward =
        collect_host_descriptors([], [Err(first.clone()), Err(second.clone())]).unwrap_err();
    let reverse = collect_host_descriptors([], [Err(second), Err(first.clone())]).unwrap_err();

    assert_eq!(forward, reverse);
    assert_eq!(forward.kind(), CollectionErrorKind::SourceOutsidePackage);
    assert_eq!(forward.detail(), first.to_string());
    assert!(
        forward
            .detail()
            .contains("/target/build/semantics/out/generated.rs")
    );
    assert!(forward.detail().contains("src/lib.rs:3:7"));
    assert!(forward.source_range().is_none());
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
    let bundle = collect_descriptors(
        [package.context("ORG-STABLE-API")],
        [
            package.sort("Expr", expr_type, vec![]),
            package.constructor("PublicValue", foo_type, expr_type),
        ],
    )
    .unwrap();
    assert_canonical_contract(&bundle);
    let expr = bundle
        .declarations()
        .iter()
        .find(|declaration| declaration.id().item_name() == "Expr")
        .unwrap();
    assert_eq!(expr.visibility, RustVisibility::Public);
    assert_eq!(expr.explicit_symbol.as_ref().unwrap().as_str(), "api::Expr");
    let value = bundle
        .declarations()
        .iter()
        .find(|declaration| declaration.id().item_name() == "PublicValue")
        .unwrap();
    assert_eq!(value.visibility, RustVisibility::Public);
    assert_eq!(
        value.explicit_symbol.as_ref().unwrap().as_str(),
        "api::PublicValue"
    );
    for descriptor in bundle.descriptors() {
        assert!(descriptor.provenance().origins().iter().any(|origin| {
            origin.key.role() == ProvenanceRole::StableSymbol && origin.key.ordinal() == 0
        }));
    }
}

#[test]
fn unicode_scalar_anchors_materialize_exact_utf8_byte_ranges() {
    let package = TestPackage::new(
        "unicode_semantics",
        "const 日本: () = ();\n#[k::sort]\npub trait Expr {}\n",
    );
    let bundle = collect_descriptors(
        [package.context("ORG-UNICODE")],
        [package.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    assert_canonical_contract(&bundle);
    let authored = &bundle.descriptors()[0].origin().frames()[0];
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
    let result = collect_descriptors([package.context("ORG-LINK")], [descriptor]);
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
    let bundle = collect_descriptors(
        [first.context("ORG-FIRST"), second.context("ORG-SECOND")],
        descriptors.clone(),
    )
    .unwrap();
    assert_canonical_contract(&bundle);
    let reordered = collect_descriptors(
        [second.context("ORG-SECOND"), first.context("ORG-FIRST")],
        descriptors.into_iter().rev(),
    )
    .unwrap();
    assert_canonical_contract(&reordered);
    assert_eq!(bundle, reordered);
    assert_eq!(bundle.descriptors().len(), 3);
    assert_ne!(bundle.descriptors()[0].id(), bundle.descriptors()[1].id());
    assert_ne!(bundle.descriptors()[1].id(), bundle.descriptors()[2].id());
}

#[test]
fn unresolved_parent_and_field_references_locate_their_own_tokens() {
    let source = r#"#[k::sort]
pub trait KItem {}

#[k::sort]
pub trait Expr: KItem + Missing {}

#[k::constructor(sort = KItem, syntax = "foo({left}, {right})")]
pub struct Foo { pub left: Term<dyn KItem>, pub right: Term<dyn Absent> }
"#;
    let package = TestPackage::new("reference_ranges", source);
    let located = |descriptors: Vec<HostDescriptor>| {
        let error =
            collect_descriptors([package.context("ORG-REFERENCES")], descriptors).unwrap_err();
        assert_eq!(
            error.kind(),
            CollectionErrorKind::UnresolvedTypeReference,
            "{error}"
        );
        let range = error.source_range().expect("located reference");
        source[range.start_byte as usize..range.end_byte as usize].to_owned()
    };

    let parents = vec![
        type_ref(kitem_type, "KItem"),
        type_ref(other_type, "Missing"),
    ];
    assert_eq!(
        located(vec![
            package.sort("KItem", kitem_type, vec![]),
            package.sort("Expr", expr_type, parents),
        ]),
        "Missing"
    );

    let mut constructor = package.constructor("Foo", foo_type, kitem_type);
    let HostDescriptorPayload::Constructor(payload) = &mut constructor.payload else {
        unreachable!("constructor fixture")
    };
    payload.fields[1].sort = type_ref(other_type, "Absent");
    assert_eq!(
        located(vec![package.sort("KItem", kitem_type, vec![]), constructor]),
        "Absent"
    );
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
    let error = collect_descriptors([package.context("ORG-CHANGED")], [descriptor]).unwrap_err();
    assert_eq!(error.kind(), CollectionErrorKind::StaleAnchor);
    let range = error.source_range().expect("located stale anchor");
    assert_eq!(range.file.package().k_namespace(), "ORG-CHANGED");
    assert_eq!(range.file.package_relative_path(), "src/lib.rs");
    assert_eq!(range.start_byte, 21);
    assert_eq!(range.end_byte, 25);
}

#[test]
fn foreign_attributes_named_like_krs_entries_are_rejected() {
    for (name, source) in [
        (
            "foreign_rule",
            "#[k::sort]\npub trait Expr {}\n\n#[other::rule]\nfn rewrite() {}\n",
        ),
        (
            "imported_sort",
            "#[k::sort]\npub trait Expr {}\n\n#[sort]\npub trait Other {}\n",
        ),
    ] {
        let package = TestPackage::new(name, source);
        let error = collect_descriptors(
            [package.context("ORG-FOREIGN")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedAttribute);
        assert!(
            error.detail().contains("`src/lib.rs`:4:1")
                && (error.detail().ends_with("write `#[k::rule]` instead")
                    || error.detail().ends_with("write `#[k::sort]` instead")),
            "{name}: {}",
            error.detail()
        );
    }
}

#[test]
fn attributes_resolve_under_the_renamed_facade_only() {
    let source = "#[language_host::sort]\npub trait Expr {}\n";
    let package = TestPackage::with_facade("renamed_facade", "", "language-host", source);
    let bundle = collect_descriptors(
        [package.context("ORG-RENAMED")],
        [package.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    assert_canonical_contract(&bundle);
    assert_eq!(bundle.descriptors().len(), 1);

    let package = TestPackage::with_facade(
        "default_alias",
        "",
        "language-host",
        "#[k::sort]\npub trait Expr {}\n",
    );
    let error = collect_descriptors(
        [package.context("ORG-DEFAULT-ALIAS")],
        [package.sort("Expr", expr_type, vec![])],
    )
    .unwrap_err();
    assert_eq!(error.kind(), CollectionErrorKind::UnresolvedAttribute);
    assert!(
        error
            .detail()
            .contains("write `#[language_host::sort]` instead"),
        "{}",
        error.detail()
    );
}

#[test]
fn variant_helpers_require_a_facade_path() {
    for (name, helper) in [
        ("foreign_variant_helper", "#[other::syntax(\"value\")]"),
        ("imported_variant_helper", "#[syntax(\"value\")]"),
    ] {
        let source = format!(
            "#[k::sort]\npub trait Expr {{}}\nuse k::syntax;\n#[k::constructors]\npub enum Values {{\n    {helper}\n    Value,\n}}\n"
        );
        let package = TestPackage::new(name, &source);
        let error = collect_descriptors(
            [package.context("ORG-HELPERS")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedAttribute);
        assert!(
            error.detail().contains("write `#[k::syntax]` instead"),
            "{}",
            error.detail()
        );
    }
}

#[test]
fn nested_attribute_positions_reject_foreign_entry_names() {
    for (name, item) in [
        ("trait_member", "trait Host { #[other::rule] fn apply(); }"),
        (
            "impl_member",
            "struct Host; impl Host { #[other::rule] fn apply() {} }",
        ),
        ("field", "struct Host { #[other::cell] value: u8 }"),
        ("type_alias", "#[other::sort] type Alias = u8;"),
        ("module", "#[other::sort] mod inner {}"),
        ("parameter", "fn host(#[other::config_var] value: u8) {}"),
    ] {
        let source = format!("#[k::sort]\npub trait Expr {{}}\n{item}\n");
        let package = TestPackage::new(name, &source);
        let error = collect_descriptors(
            [package.context("ORG-NESTED-ATTRS")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap_err();
        assert_eq!(
            error.kind(),
            CollectionErrorKind::UnresolvedAttribute,
            "{name}"
        );
    }
}

#[test]
fn item_macros_require_a_facade_path() {
    for (name, invocation) in [
        ("foreign_rules", "foreign::rules! {}"),
        ("imported_rules", "use k::rules; rules! {}"),
    ] {
        let source = format!("#[k::sort]\npub trait Expr {{}}\n{invocation}\n");
        let package = TestPackage::new(name, &source);
        let error = collect_descriptors(
            [package.context("ORG-MACROS")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::UnresolvedAttribute);
        assert!(
            error.detail().contains("write `k::rules!` instead"),
            "{}",
            error.detail()
        );
    }
}

#[test]
fn item_macros_resolve_raw_and_renamed_facade_paths() {
    for (name, facade, invocation) in [
        (
            "raw_facade",
            "k",
            "r#k::rules! { for Expr; use Op::*; eval: Neg { value } => value; }",
        ),
        (
            "renamed_rules",
            "lang",
            "lang::rules! { for Expr; use Op::*; eval: Neg { value } => value; }",
        ),
        (
            "module_alias",
            "k",
            "mod inner { use k as lang; lang::sorts! { Value; } }",
        ),
    ] {
        let source = format!("#[{facade}::sort]\npub trait Expr {{}}\n{invocation}\n");
        let package = TestPackage::with_facade(name, "", facade, &source);
        let bundle = collect_descriptors(
            [package.context("ORG-MACRO-PATHS")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap();
        assert_canonical_contract(&bundle);
        assert_eq!(bundle.descriptors().len(), 1);
    }
}

#[test]
fn symbol_diagnostics_use_the_resolved_facade_name() {
    let package = TestPackage::with_facade(
        "renamed_symbol",
        "",
        "lang",
        "#[lang::symbol(\"x\")]\npub trait Expr {}\n",
    );
    let error = collect_descriptors(
        [package.context("ORG-SYMBOL")],
        [package.sort("Expr", expr_type, vec![])],
    )
    .unwrap_err();
    assert_eq!(error.kind(), CollectionErrorKind::SourceSyntax);
    assert!(
        error
            .detail()
            .contains("#[lang::symbol] requires exactly one #[lang::sort]"),
        "{}",
        error.detail()
    );
}

#[test]
fn rejects_protocol_root_duplicate_id_and_duplicate_type() {
    let package = TestPackage::new("negative", "#[k::sort]\npub trait Expr {}\n");

    let mut old = package.sort("Expr", expr_type, vec![]);
    old.protocol_version = SchemaVersion(2);
    assert_kind(
        collect_descriptors([package.context("ORG-NEG")], [old]),
        CollectionErrorKind::UnsupportedSchemaVersion,
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
        collect_descriptors([package.context("ORG-NEG")], [wrong_root]),
        CollectionErrorKind::CrateRootMismatch,
    );

    let duplicate = package.sort("Expr", expr_type, vec![]);
    assert_kind(
        collect_descriptors([package.context("ORG-NEG")], [duplicate.clone(), duplicate]),
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
        collect_descriptors(
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
        collect_descriptors(
            [package.context("ORG-ONE"), package.context("ORG-TWO")],
            [package.sort("Expr", expr_type, vec![])],
        ),
        CollectionErrorKind::DuplicatePackageContext,
    );

    let other = TestPackage::new("other_context", "#[k::sort]\npub trait Expr {}\n");
    assert_kind(
        collect_descriptors(
            [package.context("ORG-SAME"), other.context("ORG-SAME")],
            std::iter::empty(),
        ),
        CollectionErrorKind::DuplicateKNamespace,
    );

    let mut missing_type = package.sort("Expr", expr_type, vec![]);
    missing_type.declared_type = None;
    assert_kind(
        collect_descriptors([package.context("ORG-MISSING")], [missing_type]),
        CollectionErrorKind::MissingTypeDeclaration,
    );
}

#[test]
fn rejects_wrong_display_out_of_bounds_and_imprecise_anchors() {
    let package = TestPackage::new("anchors", "#[k::sort]\npub trait Expr {}\n");
    let mut wrong_file = package.sort("Expr", expr_type, vec![]);
    wrong_file.provenance = replace_display(&wrong_file.provenance, "src/missing.rs");
    assert_kind(
        collect_descriptors([package.context("ORG-ANCHOR")], [wrong_file]),
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
        collect_descriptors([package.context("ORG-ANCHOR")], [out_of_bounds]),
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
        collect_descriptors([package.context("ORG-ANCHOR")], [imprecise]),
        CollectionErrorKind::ImpreciseAuthoredAnchor,
    );
}

#[cfg(unix)]
#[test]
fn source_symlinks_cannot_escape_the_canonical_package_directory() {
    let package = TestPackage::new("escape", "#[k::sort]\npub trait Expr {}\n");
    let external = temp_dir();
    let external_source = external.path().join("outside.rs");
    fs::write(&external_source, "#[k::sort]\npub trait Expr {}\n").unwrap();
    std::os::unix::fs::symlink(&external_source, package.root().join("src/escape.rs")).unwrap();
    let mut descriptor = package.sort("Expr", expr_type, vec![]);
    descriptor.provenance = replace_display(&descriptor.provenance, "src/escape.rs");
    assert_kind(
        collect_descriptors([package.context("ORG-ESCAPE")], [descriptor]),
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
    let package_bundle = collect_descriptors(
        [package.context("ORG-WORKSPACE-HINT")],
        [package_descriptor.clone()],
    )
    .unwrap();
    assert_canonical_contract(&package_bundle);
    let workspace_hint = package
        .root()
        .strip_prefix(package.directory.path())
        .unwrap()
        .join("src/lib.rs")
        .to_string_lossy()
        .replace('\\', "/");
    let mut workspace_descriptor = package_descriptor;
    workspace_descriptor.provenance =
        replace_display(&workspace_descriptor.provenance, &workspace_hint);
    let workspace_bundle = collect_descriptors(
        [package.context("ORG-WORKSPACE-HINT")],
        [workspace_descriptor],
    )
    .unwrap();
    assert_canonical_contract(&workspace_bundle);

    assert_eq!(package_bundle, workspace_bundle);
    let krs_ir::OriginFrame::Ranged { range, .. } =
        &workspace_bundle.descriptors()[0].origin().frames()[0]
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
    let bundle = collect_descriptors([package.context("ORG-ALIAS")], [descriptor]).unwrap();
    assert_canonical_contract(&bundle);
    let krs_ir::OriginFrame::Ranged { range, .. } = &bundle.descriptors()[0].origin().frames()[0]
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
        collect_descriptors([package.context("ORG-SOURCE-AMBIGUITY")], [descriptor]),
        CollectionErrorKind::AmbiguousSourcePath,
    );
}

#[test]
fn duplicate_reparsed_invocations_are_rejected_as_ambiguous() {
    let package = TestPackage::new("ambiguous", "#[k::sort]\n#[k::sort]\npub trait Expr {}\n");
    assert_kind(
        collect_descriptors(
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
    let _ = k::cells! { k: KCell(value /*krs-f7-block*/, ..tail), ..state };
}
",
            "cells!",
        ),
        (
            "dsl_block_map",
            r"#[k::sort]
pub trait Expr {}
fn fixture() {
    let _ = k::map! { name /*krs-f7-block*/ -> value, rest @ .. };
}
",
            "map!",
        ),
    ];
    for (name, source, diagnostic_macro) in cases {
        let package = TestPackage::new(name, source);
        let error = collect_descriptors(
            [package.context("KRS-F7-COLLECTOR")],
            [package.sort("Expr", expr_type, vec![])],
        )
        .unwrap_err();
        assert_eq!(error.kind(), CollectionErrorKind::SourceSyntax);
        let start = source.find("/*krs-f7-block*/").unwrap();
        let end = start + "/*krs-f7-block*/".len();
        let range = error.source_range().expect("located trivia failure");
        assert_eq!(range.start_byte as usize, start);
        assert_eq!(range.end_byte as usize, end);
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
    let _ = k::cells! {
        k: KCell(value, // preserve the continuation
            ..tail),
        ..state
    };
    let _ = k::map! {
        name -> value, // preserve the remainder
        rest @ ..
    };
}
";
    let baseline = TestPackage::new("dsl_line_comments", baseline_source);
    let commented = TestPackage::new("dsl_line_comments", commented_source);
    let baseline_bundle = collect_descriptors(
        [baseline.context("KRS-F7-COLLECTOR")],
        [baseline.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    assert_canonical_contract(&baseline_bundle);
    let commented_bundle = collect_descriptors(
        [commented.context("KRS-F7-COLLECTOR")],
        [commented.sort("Expr", expr_type, vec![])],
    )
    .unwrap();
    assert_canonical_contract(&commented_bundle);
    let baseline_descriptor = &baseline_bundle.descriptors()[0];
    let commented_descriptor = &commented_bundle.descriptors()[0];
    assert_eq!(baseline_descriptor.id(), commented_descriptor.id());
    assert_eq!(
        baseline_descriptor.payload(),
        commented_descriptor.payload()
    );
    let topology = |descriptor: &krs_ir::Descriptor| {
        descriptor
            .provenance()
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

fn assert_kind(
    result: Result<krs_ir::DescriptorBundle, krs_collector::CollectionError>,
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
    directory: TempDir,
    package_root: PathBuf,
    name: String,
    source: String,
}

impl TestPackage {
    fn new(name: &str, source: &str) -> Self {
        Self::new_nested(name, "", source)
    }

    fn new_nested(name: &str, relative_root: &str, source: &str) -> Self {
        Self::with_facade(name, relative_root, "k", source)
    }

    /// A package whose manifest names the `krs` facade `facade`.
    fn with_facade(name: &str, relative_root: &str, facade: &str, source: &str) -> Self {
        let directory = temp_dir();
        let package_root = directory.path().join(relative_root);
        fs::create_dir_all(package_root.join("src")).unwrap();
        fs::write(
            package_root.join("Cargo.toml"),
            format!(
                "[package]\nname = \"{name}\"\nversion = \"0.1.0\"\n\n[dependencies]\n{facade} = {{ package = \"krs\", path = \"krs\" }}\n"
            ),
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
            .find(|attribute| is_symbol_attribute(attribute))
            .map(|attribute| {
                krs_syntax::SymbolAttribute::parse_tokens(attribute_tokens(attribute)).unwrap()
            });
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
            protocol_version: SchemaVersion::CURRENT,
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
        let parsed = krs_syntax::ConstructorAttribute::parse_tokens(list.tokens.clone()).unwrap();
        let declaration = ConstructorDeclaration::from_item(item.clone()).unwrap();
        let mut provenance = parsed.provenance().unwrap();
        provenance.extend(declaration.provenance().unwrap());
        if let Some(symbol) = item
            .attrs
            .iter()
            .find(|attribute| is_symbol_attribute(attribute))
        {
            provenance.extend(
                krs_syntax::SymbolAttribute::parse_tokens(attribute_tokens(symbol))
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
            protocol_version: SchemaVersion::CURRENT,
            id: self.item_id(name, ItemKind::Constructor, &[]),
            declared_type: Some(krs_ir::HostDeclarationIdentity::Nominal(HostTypeKey(
                declared,
            ))),
            payload: HostDescriptorPayload::Constructor(HostConstructorDescriptor {
                parameters: Vec::new(),
                sort: krs_ir::HostSortReference {
                    key: krs_ir::ProvenanceKey::new(ProvenanceRole::ConstructorSort, 0),
                    target: type_ref(sort, "Expr"),
                },
                fields,
            }),
            cfg: BTreeMap::new(),
            provenance: host_provenance("src/lib.rs", provenance),
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
                anchor.key(),
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
    let start = Position::from_proc_macro2(start).unwrap();
    let end = Position::from_proc_macro2(end).unwrap();
    HostSourceAnchor::new(
        display,
        HostSourcePosition::new(start.line(), start.scalar_column()).unwrap(),
        HostSourcePosition::new(end.line(), end.scalar_column()).unwrap(),
        precision,
    )
    .unwrap()
}
