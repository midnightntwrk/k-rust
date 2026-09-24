use std::any::TypeId;
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use krs_compiler::{PackageContext, collect_host_descriptors};
use krs_ir::{
    AnchorPrecision, HostAuthoredAnchor, HostDeclarationIdentity, HostDescriptor,
    HostDescriptorPayload, HostItemId, HostPackageKey, HostProvenance, HostSortDescriptor,
    HostSourceAnchor, HostSourcePosition, HostTypeKey, ItemKind, SchemaVersion, ProvenanceKey,
};

struct ExprType;

fn expr_type() -> TypeId {
    TypeId::of::<ExprType>()
}

fn position(line: u32, scalar_column: u32) -> HostSourcePosition {
    HostSourcePosition::new(line, scalar_column).expect("fixture positions are nonzero")
}

fn anchor(display_file: &str, line: u32, start: u32, end: u32) -> HostSourceAnchor {
    HostSourceAnchor::new(
        display_file,
        position(line, start),
        position(line, end),
        AnchorPrecision::Exact,
    )
    .expect("fixture anchor is ordered")
}

fn descriptor(package_root: &Path, display_file: &str) -> HostDescriptor {
    let key = ProvenanceKey::new("sort_declaration", 0).expect("known provenance role");
    let authored = HostAuthoredAnchor::new(key, anchor(display_file, 2, 11, 15));
    let provenance = HostProvenance::new(anchor(display_file, 1, 1, 11), vec![authored])
        .expect("fixture provenance is complete");
    HostDescriptor {
        protocol_version: SchemaVersion::CURRENT,
        id: HostItemId::new(
            HostPackageKey::new("diagnostic-anchor", "0.0.0", package_root)
                .expect("fixture package key"),
            ["diagnostic_anchor"],
            "Expr",
            ItemKind::Sort,
            "",
        )
        .expect("fixture item identity"),
        declared_type: Some(HostDeclarationIdentity::Nominal(HostTypeKey(expr_type))),
        payload: HostDescriptorPayload::Sort(HostSortDescriptor {
            parents: Vec::new(),
        }),
        cfg: BTreeMap::new(),
        provenance,
    }
}

fn main() {
    let case = std::env::args()
        .nth(1)
        .expect("usage: anchor-probe stale|missing");
    let package_root = Path::new("/var/tmp/krs-diagnostics-anchor-target/anchor-package");
    if package_root.exists() {
        fs::remove_dir_all(package_root).expect("remove prior isolated fixture");
    }
    fs::create_dir_all(package_root.join("src")).expect("create isolated fixture");
    fs::write(
        package_root.join("Cargo.toml"),
        "[package]\nname = \"diagnostic-anchor\"\nversion = \"0.0.0\"\n\n[dependencies]\nk = { package = \"krs\", path = \"krs\" }\n",
    )
    .expect("write manifest");
    fs::write(
        package_root.join("src/lib.rs"),
        "#[k::sort]\npub trait Expr {}\n",
    )
    .expect("write authored source");

    let (display_file, mutate) = match case.as_str() {
        "stale" => ("src/lib.rs", true),
        "missing" => ("src/missing.rs", false),
        _ => panic!("usage: anchor-probe stale|missing"),
    };
    let host = descriptor(package_root, display_file);
    if mutate {
        fs::write(
            package_root.join("src/lib.rs"),
            "#[k::sort]\npub trait Changed {}\n",
        )
        .expect("replace source after expansion anchor capture");
    }
    let context = PackageContext::new(
        "DIAGNOSTIC-ANCHOR",
        "diagnostic-anchor",
        "0.0.0",
        "workspace",
        "diagnostic_anchor",
        package_root.join("Cargo.toml"),
    )
    .expect("fixture package context");
    let error = collect_host_descriptors([context], [host])
        .expect_err("negative anchor case must fail collection");
    println!(
        "{}",
        serde_json::json!({
            "case": case,
            "kind": format!("{:?}", error.kind()),
            "detail": error.detail(),
        })
    );
}
