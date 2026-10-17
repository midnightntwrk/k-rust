//! kink's semantics identity (packet CACHE-ID): every versioned constant of every workspace
//! member is either a component of the identity or listed outside it with a reason, and the
//! identity is the object every store keys on. Packet CACHE-ID-fix-1 (CACHE-ID review 1 minors 1
//! and 3): the scan parses the sources (syn), so it sees `static` items, items inside blocks and
//! `impl`s, raw strings and any literal text; it reads the members from the workspace's
//! Cargo.toml; and the k-rust snapshot Cargo.toml builds against is the pinned revision.

use kink_campaign::identity::{
    KINK_IDENTITY, OUTSIDE_IDENTITY, build_identity_of, identity_difference, kink_build,
    kink_identity, writer_difference,
};
use serde_json::json;
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};
use syn::visit::Visit;

/// The value of a `const` or `static` item, as far as the scan reads it.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Written {
    /// A string literal (raw or not), unescaped.
    Str(String),
    /// An integer literal, its digits.
    Int(String),
    /// A path: another constant's name (its last segment).
    Alias(String),
    /// Anything else (a call, a macro such as `concat!`, a struct, ...).
    Other,
}

/// A `const` or `static` item: whether its type is `&str`, and its value.
#[derive(Clone, Debug)]
struct Item {
    is_str: bool,
    value: Written,
}

/// Every `const` and `static` item of every member: `(package, NAME) -> Item`. Items of one
/// name in one package (for example in two test modules) keep the first; the classification is
/// by name.
type Items = BTreeMap<(String, String), Item>;

fn rust_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            rust_files(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }
}

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn cargo_toml(path: &Path) -> toml::Table {
    toml::from_str(&fs::read_to_string(path).unwrap()).unwrap()
}

/// `(package name, directory)` of every member of the workspace, from its Cargo.toml.
fn members() -> Vec<(String, PathBuf)> {
    let root = cargo_toml(&workspace().join("Cargo.toml"));
    root["workspace"]["members"]
        .as_array()
        .unwrap()
        .iter()
        .map(|member| {
            let directory = workspace().join(member.as_str().unwrap());
            let package = cargo_toml(&directory.join("Cargo.toml"));
            (
                package["package"]["name"].as_str().unwrap().to_owned(),
                directory,
            )
        })
        .collect()
}

fn written(expr: &syn::Expr) -> Written {
    match expr {
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(literal),
            ..
        }) => Written::Str(literal.value()),
        syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(literal),
            ..
        }) => Written::Int(literal.base10_digits().to_owned()),
        syn::Expr::Path(path) => Written::Alias(
            path.path
                .segments
                .last()
                .map(|segment| segment.ident.to_string())
                .unwrap_or_default(),
        ),
        syn::Expr::Group(group) => written(&group.expr),
        syn::Expr::Paren(paren) => written(&paren.expr),
        _ => Written::Other,
    }
}

fn is_str(ty: &syn::Type) -> bool {
    matches!(ty, syn::Type::Reference(reference)
        if matches!(&*reference.elem, syn::Type::Path(path) if path.path.is_ident("str")))
}

struct Collector<'a> {
    package: &'a str,
    items: &'a mut Items,
}

impl Collector<'_> {
    fn add(&mut self, name: &syn::Ident, ty: &syn::Type, expr: &syn::Expr) {
        self.items
            .entry((self.package.to_owned(), name.to_string()))
            .or_insert(Item {
                is_str: is_str(ty),
                value: written(expr),
            });
    }
}

impl<'ast> Visit<'ast> for Collector<'_> {
    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        self.add(&item.ident, &item.ty, &item.expr);
        syn::visit::visit_item_const(self, item);
    }
    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        self.add(&item.ident, &item.ty, &item.expr);
        syn::visit::visit_item_static(self, item);
    }
    fn visit_impl_item_const(&mut self, item: &'ast syn::ImplItemConst) {
        self.add(&item.ident, &item.ty, &item.expr);
        syn::visit::visit_impl_item_const(self, item);
    }
    fn visit_trait_item_const(&mut self, item: &'ast syn::TraitItemConst) {
        if let Some((_, expr)) = &item.default {
            self.add(&item.ident, &item.ty, expr);
        }
        syn::visit::visit_trait_item_const(self, item);
    }
}

/// Every `const` and `static` item of every member's `src/` (and `build.rs`), parsed.
fn items() -> Items {
    let mut items = Items::new();
    for (package, directory) in members() {
        let mut files = Vec::new();
        rust_files(&directory.join("src"), &mut files);
        let build = directory.join("build.rs");
        if build.is_file() {
            files.push(build);
        }
        for file in files {
            let syntax = syn::parse_file(&fs::read_to_string(&file).unwrap())
                .unwrap_or_else(|e| panic!("{}: {e}", file.display()));
            Collector {
                package: &package,
                items: &mut items,
            }
            .visit_file(&syntax);
        }
    }
    items
}

/// A name that looks versioned: it ends in `_VERSION` or `_DOMAIN`.
fn versioned_name(name: &str) -> bool {
    name.ends_with("_VERSION") || name.ends_with("_DOMAIN")
}

/// A literal that ends in a version: `/v<N>`, `/v<N>.<M>...` or `-v<N>`.
fn versioned_literal(literal: &str) -> bool {
    let digits = |text: &str| !text.is_empty() && text.chars().all(|c| c.is_ascii_digit());
    let dotted = literal
        .rsplit_once("/v")
        .is_some_and(|(_, rest)| rest.split('.').all(digits));
    let dashed = literal
        .rsplit_once("-v")
        .is_some_and(|(_, rest)| digits(rest));
    dotted || dashed
}

/// The versioned items: a versioned-looking name, a string value ending in a version, or a value
/// that names another versioned item (an alias, followed to its end).
fn versioned(items: &Items) -> BTreeSet<(String, String)> {
    let mut versioned = items
        .iter()
        .filter(|((_, name), item)| {
            versioned_name(name)
                || matches!(&item.value, Written::Str(literal) if versioned_literal(literal))
        })
        .map(|(id, _)| id.clone())
        .collect::<BTreeSet<_>>();
    loop {
        let names = versioned
            .iter()
            .map(|(_, name)| name.clone())
            .collect::<BTreeSet<_>>();
        let aliases = items
            .iter()
            .filter(|(id, item)| {
                !versioned.contains(*id)
                    && matches!(&item.value, Written::Alias(target)
                        if names.contains(target) || versioned_name(target))
            })
            .map(|(id, _)| id.clone())
            .collect::<Vec<_>>();
        if aliases.is_empty() {
            return versioned;
        }
        versioned.extend(aliases);
    }
}

#[test]
fn the_scan_sees_every_shape_of_a_version() {
    let source = r##"
        static STATIC_VERSION: &str = "kink/x/v1";
        const ALIAS: &str = OTHER_DOMAIN;
        const CONCAT_VERSION: &str = concat!("kink/", "v1");
        const DOTTED: &str = "kink/x/v1.1";
        const DASHED: &str = "kink-x-v2";
        const RAW: &str = r"kink/x/v2";
        const SEMI: &str = "a;b/v3";
        const NUMERIC_VERSION: u64 = 3;
        const PLAIN: &str = "kink/x/vector";
        impl X { const IMPL_DOMAIN: &str = "kink/impl/v1"; }
        fn f() { const INNER: &str = "kink/inner/v4"; }
    "##;
    let mut items = Items::new();
    Collector {
        package: "probe",
        items: &mut items,
    }
    .visit_file(&syn::parse_file(source).unwrap());
    let found = versioned(&items)
        .into_iter()
        .map(|(_, name)| name)
        .collect::<Vec<_>>();
    assert_eq!(
        found,
        [
            "ALIAS",
            "CONCAT_VERSION",
            "DASHED",
            "DOTTED",
            "IMPL_DOMAIN",
            "INNER",
            "NUMERIC_VERSION",
            "RAW",
            "SEMI",
            "STATIC_VERSION",
        ]
    );
    assert_eq!(
        items[&("probe".to_owned(), "SEMI".to_owned())].value,
        Written::Str("a;b/v3".into())
    );
    assert_eq!(
        items[&("probe".to_owned(), "CONCAT_VERSION".to_owned())].value,
        Written::Other
    );
}

#[test]
fn every_versioned_constant_is_in_the_identity_or_listed_outside_it() {
    let items = items();
    let inside = KINK_IDENTITY
        .iter()
        .map(|c| (c.krate.to_owned(), c.constant.to_owned()))
        .collect::<BTreeSet<_>>();
    let outside = OUTSIDE_IDENTITY
        .iter()
        .map(|c| (c.krate.to_owned(), c.constant.to_owned()))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        inside.len(),
        KINK_IDENTITY.len(),
        "a component is named twice"
    );
    assert_eq!(
        outside.len(),
        OUTSIDE_IDENTITY.len(),
        "an exemption is listed twice"
    );
    assert!(inside.is_disjoint(&outside));
    let keys = KINK_IDENTITY.iter().map(|c| c.key).collect::<BTreeSet<_>>();
    assert_eq!(keys.len(), KINK_IDENTITY.len(), "a key is used twice");
    let versioned = versioned(&items);
    // Every versioned constant is classified. A failure here is a new version constant: add it
    // to KINK_IDENTITY when its change can change a verdict, else to OUTSIDE_IDENTITY with the
    // reason it cannot (naming the path that checks it).
    let unclassified = versioned
        .iter()
        .filter(|id| !inside.contains(*id) && !outside.contains(*id))
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(unclassified, Vec::<(String, String)>::new());
    // A versioned-looking name is written as a literal, so the scan and a reader see its value.
    let computed = items
        .iter()
        .filter(|((_, name), item)| {
            versioned_name(name) && !matches!(item.value, Written::Str(_) | Written::Int(_))
        })
        .map(|(id, _)| id.clone())
        .collect::<Vec<_>>();
    assert_eq!(computed, Vec::<(String, String)>::new());
    // Every listed constant exists, so neither list keeps a stale entry, and every component's
    // value is its constant's literal.
    for component in KINK_IDENTITY {
        let id = (component.krate.to_owned(), component.constant.to_owned());
        let item = items
            .get(&id)
            .unwrap_or_else(|| panic!("{id:?} is not a constant of its crate"));
        assert!(item.is_str, "{id:?}");
        assert_eq!(
            item.value,
            Written::Str(component.value.to_owned()),
            "{id:?}"
        );
    }
    for exemption in OUTSIDE_IDENTITY {
        let id = (exemption.krate.to_owned(), exemption.constant.to_owned());
        assert!(
            items.contains_key(&id),
            "{id:?} is not a constant of its crate"
        );
        assert!(versioned.contains(&id), "{id:?} is not versioned");
        assert!(!exemption.reason.is_empty(), "{id:?}");
    }
    // The scan sees the constants it must, so a broken scan cannot pass by finding nothing: the
    // version constants at the time of CACHE-ID, every member, and an alias.
    assert_eq!(
        members()
            .into_iter()
            .map(|(package, _)| package)
            .collect::<Vec<_>>(),
        [
            "kink-campaign",
            "kink-corpus",
            "kink-flow",
            "kink-native",
            "kink-patch",
            "kink-pattern",
        ]
    );
    for id in [
        ("kink-patch", "CLAIM_REMOVAL_VERSION"),
        ("kink-native", "DEFINITION_EXCLUSION_VERSION"),
        ("kink-native", "EXECUTION_REQUEST_VERSION"),
        ("kink-campaign", "CAMPAIGN_REPORT_VERSION"),
        ("kink-flow", "RUN_VERSION"),
        ("kink-flow", "OUTCOME_SCHEMA_VERSION"),
        ("kink-flow", "EXECUTION_DIGEST_KIND"),
    ] {
        let id = (id.0.to_owned(), id.1.to_owned());
        assert!(versioned.contains(&id), "{id:?}");
    }
}

/// CACHE-ID review 1 minor 3: the k-rust and k-rust-backend snapshots Cargo.toml builds against
/// are named by K_RUST_REVISION's prefix (`../k-rust-<prefix>/...`), so a re-pin that moves the
/// path without the constant (which the semantics identity names) fails here.
#[test]
fn the_k_rust_snapshot_cargo_builds_against_is_the_pinned_revision() {
    let root = cargo_toml(&workspace().join("Cargo.toml"));
    for package in ["k-rust", "k-rust-backend"] {
        let path = root["workspace"]["dependencies"][package]["path"]
            .as_str()
            .unwrap();
        let snapshot = Path::new(path)
            .components()
            .find_map(|part| part.as_os_str().to_str()?.strip_prefix("k-rust-"))
            .unwrap_or_else(|| panic!("{package}: {path} names no k-rust snapshot"));
        assert!(
            snapshot.len() >= 8
                && snapshot.chars().all(|c| c.is_ascii_hexdigit())
                && kink_native::K_RUST_REVISION.starts_with(snapshot),
            "{package}: {path} is not k-rust {}",
            kink_native::K_RUST_REVISION
        );
    }
}

/// Packet CACHE-ID-fix-1: the build identity is the executable's digest, an unreadable
/// executable has none, and a record is honoured only when it names this build; the reason
/// names both builds and the first identity component that differs.
#[test]
fn a_record_is_honoured_only_by_the_build_that_wrote_it() {
    let this = kink_build().unwrap();
    assert_eq!(
        build_identity_of(&std::env::current_exe().unwrap()),
        Ok(this)
    );
    assert!(build_identity_of(Path::new("/nonexistent/kink-build")).is_err());
    let identity = kink_identity();
    let build = Ok(this);
    assert_eq!(
        writer_difference(&json!(this.to_string()), &identity, &build),
        None
    );
    let other = kink_patch::sha256(b"another build").to_string();
    let reason = writer_difference(&json!(other), &identity, &build).unwrap();
    assert!(
        reason.contains(&other) && reason.contains(&this.to_string()),
        "{reason}"
    );
    assert!(
        reason.contains("its kink identity is this build's"),
        "{reason}"
    );
    let mut changed = identity.clone();
    changed["patch_admission"] = json!("kink-patch/patch-admission/v0");
    let reason = writer_difference(&json!(other), &changed, &build).unwrap();
    assert!(reason.contains("differs at `patch_admission`"), "{reason}");
    let reason = writer_difference(&json!(null), &identity, &build).unwrap();
    assert!(reason.contains("does not name"), "{reason}");
    let unknown = Err("cannot read the executable".to_owned());
    assert!(writer_difference(&json!(this.to_string()), &identity, &unknown).is_some());
    assert!(writer_difference(&json!(null), &identity, &unknown).is_some());
}

#[test]
fn the_identity_is_an_object_of_its_components() {
    let identity = kink_identity();
    let object = identity.as_object().unwrap();
    assert_eq!(object.len(), KINK_IDENTITY.len());
    for component in KINK_IDENTITY {
        assert_eq!(
            object[component.key],
            json!(component.value),
            "{}",
            component.key
        );
    }
    assert_eq!(identity["k_rust_revision"], kink_native::K_RUST_REVISION);
    assert_eq!(
        identity["definition_exclusion"],
        kink_native::exclusion::DEFINITION_EXCLUSION_VERSION
    );
    // Re-pin L1-2-land: the one-sided kill rule is a component, and an identity written before
    // it (830c18e: every other component equal) differs at it.
    assert_eq!(identity["one_sided"], kink_campaign::ONE_SIDED_VERSION);
    let mut before = identity.clone();
    before.as_object_mut().unwrap().remove("one_sided");
    assert_eq!(identity_difference(&before).as_deref(), Some("one_sided"));
    assert_eq!(identity_difference(&identity), None);
    // Re-pin L2-1: coverage v2 (equations, matched and applied) is another coverage reading, so
    // an identity written under v1 (f0fc3a1: every other component equal) differs at it, and
    // every store keyed on the identity misses or refuses it.
    assert_eq!(identity["coverage"], "kink/coverage/v2");
    let mut v1 = identity.clone();
    v1["coverage"] = json!("kink/coverage/v1");
    assert_eq!(identity_difference(&v1).as_deref(), Some("coverage"));
    for component in KINK_IDENTITY {
        let mut changed = identity.clone();
        changed[component.key] = json!(format!("{}-other", component.value));
        assert_eq!(
            identity_difference(&changed).as_deref(),
            Some(component.key)
        );
        let mut missing = identity.clone();
        missing.as_object_mut().unwrap().remove(component.key);
        assert_eq!(
            identity_difference(&missing).as_deref(),
            Some(component.key)
        );
    }
    let mut extra = identity.clone();
    extra["later_algorithm"] = json!("kink/later/v1");
    assert_eq!(
        identity_difference(&extra).as_deref(),
        Some("later_algorithm")
    );
    assert_eq!(identity_difference(&json!(null)).as_deref(), Some(""));
}
