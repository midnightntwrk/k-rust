//! Policy fixtures (versions 1 and 2), lesson acceptance, and allowlist drift.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use krs_lesson_policy::{
    LessonPolicy, PolicyDiagnostic, SUPPORTED_VERSIONS, check, check_request, protocol, v1, v2,
};

fn fixtures_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
}

struct Expected {
    code: String,
    start: usize,
    end: usize,
    text: String,
}

struct Fixture {
    name: String,
    /// Policy versions the fixture applies to (default: every version).
    versions: Vec<u32>,
    display_file: String,
    editable_files: Vec<String>,
    source: String,
    expected: Vec<Expected>,
}

fn string(table: &toml_edit::Table, key: &str, fixture: &str) -> String {
    table
        .get(key)
        .and_then(toml_edit::Item::as_str)
        .unwrap_or_else(|| panic!("{fixture}: `{key}` must be a string"))
        .to_owned()
}

fn integer(table: &toml_edit::Table, key: &str, fixture: &str) -> usize {
    let value = table
        .get(key)
        .and_then(toml_edit::Item::as_integer)
        .unwrap_or_else(|| panic!("{fixture}: `{key}` must be an integer"));
    usize::try_from(value).expect("offsets are non-negative")
}

fn load_fixtures() -> Vec<Fixture> {
    let mut directories: Vec<PathBuf> = std::fs::read_dir(fixtures_root())
        .expect("fixture directory exists")
        .map(|entry| entry.expect("fixture entry").path())
        .filter(|path| path.is_dir())
        .collect();
    directories.sort();
    directories
        .into_iter()
        .map(|directory| {
            let name = directory
                .file_name()
                .and_then(|name| name.to_str())
                .expect("UTF-8 fixture name")
                .to_owned();
            let source = std::fs::read_to_string(directory.join("source.rs"))
                .unwrap_or_else(|error| panic!("{name}: source.rs: {error}"));
            let manifest = std::fs::read_to_string(directory.join("expected.toml"))
                .unwrap_or_else(|error| panic!("{name}: expected.toml: {error}"));
            let document: toml_edit::Document<String> = manifest
                .parse()
                .unwrap_or_else(|error| panic!("{name}: expected.toml: {error}"));
            let root = document.as_table();
            let display_file = root
                .get("display_file")
                .and_then(toml_edit::Item::as_str)
                .unwrap_or("src/lib.rs")
                .to_owned();
            let versions = root
                .get("versions")
                .and_then(toml_edit::Item::as_array)
                .map_or_else(
                    || SUPPORTED_VERSIONS.to_vec(),
                    |array| {
                        array
                            .iter()
                            .map(|value| {
                                u32::try_from(value.as_integer().expect("version integer"))
                                    .expect("small version")
                            })
                            .collect()
                    },
                );
            let editable_files = root
                .get("editable_files")
                .and_then(toml_edit::Item::as_array)
                .map_or_else(
                    || vec!["src/lib.rs".to_owned()],
                    |array| {
                        array
                            .iter()
                            .map(|value| value.as_str().expect("path string").to_owned())
                            .collect()
                    },
                );
            let expected = root
                .get("diagnostic")
                .and_then(toml_edit::Item::as_array_of_tables)
                .map(|tables| {
                    tables
                        .iter()
                        .map(|table| Expected {
                            code: string(table, "code", &name),
                            start: integer(table, "start", &name),
                            end: integer(table, "end", &name),
                            text: string(table, "text", &name),
                        })
                        .collect()
                })
                .unwrap_or_default();
            Fixture {
                name,
                versions,
                display_file,
                editable_files,
                source,
                expected,
            }
        })
        .collect()
}

fn policy_for(fixture: &Fixture, version: u32) -> LessonPolicy {
    LessonPolicy {
        version,
        editable_files: fixture.editable_files.clone(),
        ..LessonPolicy::single_file_v1()
    }
}

fn observed_line(diagnostic: &PolicyDiagnostic) -> String {
    match &diagnostic.authored {
        Some(range) => format!("{} {}..{}", diagnostic.code, range.start, range.end),
        None => format!("{} (request level)", diagnostic.code),
    }
}

#[test]
fn every_fixture_yields_exactly_its_expected_diagnostics() {
    let fixtures = load_fixtures();
    assert!(!fixtures.is_empty(), "no fixtures found");
    let mut failures = Vec::new();
    let mut report = String::from(
        "# Generated by crates/krs-lesson-policy/tests/policy.rs.\n# Each fixture's expected and observed diagnostics.\n",
    );
    for fixture in &fixtures {
        for expected in &fixture.expected {
            let authored = fixture.source.get(expected.start..expected.end);
            if authored != Some(expected.text.as_str()) {
                failures.push(format!(
                    "{}: expected.toml text {:?} does not match source bytes {}..{} ({authored:?})",
                    fixture.name, expected.text, expected.start, expected.end
                ));
            }
        }
        let expected_lines: Vec<String> = fixture
            .expected
            .iter()
            .map(|expected| format!("{} {}..{}", expected.code, expected.start, expected.end))
            .collect();
        for &version in &fixture.versions {
            let observed = check(
                &fixture.source,
                &fixture.display_file,
                &policy_for(fixture, version),
            );
            let observed_lines: Vec<String> = observed.iter().map(observed_line).collect();
            let matches = observed_lines == expected_lines;
            if !matches {
                failures.push(format!(
                    "{} (version {version}): expected {expected_lines:?}, observed {observed_lines:?}\n{:#?}",
                    fixture.name, observed
                ));
            }
            for diagnostic in &observed {
                assert_eq!(diagnostic.class, "exact-authored", "{}", fixture.name);
                assert_eq!(diagnostic.file, fixture.display_file, "{}", fixture.name);
            }
            let _ = writeln!(
                report,
                "\n[[fixture]]\nname = {:?}\nversion = {version}\nmatches = {matches}",
                fixture.name
            );
            let _ = writeln!(
                report,
                "expected = {expected_lines:?}\nobserved = {observed_lines:?}"
            );
        }
    }
    if let Some(path) = std::env::var_os("KRS_LESSON_POLICY_FIXTURE_RESULTS") {
        std::fs::write(path, report).expect("fixture results are writable");
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

#[test]
fn every_code_has_a_rejecting_and_an_accepted_fixture() {
    let fixtures = load_fixtures();
    for (version, codes) in [(1, v1::CODES), (2, v2::CODES)] {
        let mut rejected = BTreeSet::new();
        let mut near_misses = BTreeSet::new();
        for fixture in fixtures
            .iter()
            .filter(|fixture| fixture.versions.contains(&version))
        {
            for expected in &fixture.expected {
                rejected.insert(expected.code.clone());
            }
            if fixture.expected.is_empty()
                && let Some(code) = fixture.name.strip_suffix("-accepted")
            {
                near_misses.insert(format!("krs::policy::{code}"));
            }
        }
        // Request-level codes are exercised by `check_request` tests below.
        for code in codes.iter().filter(|code| **code != v1::EDITABLE_FILE) {
            assert!(
                rejected.contains(*code),
                "no version {version} fixture rejecting {code}"
            );
            if *code != v1::PARSE {
                assert!(
                    near_misses.contains(*code),
                    "no version {version} accepted near-miss fixture for {code}"
                );
            }
        }
    }
}

/// Each allowlist that version 2 widened has a version 2 fixture that is
/// rejected just outside the new entry and one that is accepted, and a
/// version 1 fixture showing that version 1 still rejects the entry.
#[test]
fn every_version_2_allowlist_change_has_fixtures() {
    let fixtures = load_fixtures();
    let find = |name: &str| {
        fixtures
            .iter()
            .find(|fixture| fixture.name == name)
            .unwrap_or_else(|| panic!("missing fixture {name}"))
    };
    for change in ["tool-attribute", "variant-attribute"] {
        let rejected = find(change);
        assert!(rejected.versions.contains(&2) && !rejected.expected.is_empty());
        let accepted = find(&format!("{change}-accepted"));
        assert!(accepted.versions.contains(&2) && accepted.expected.is_empty());
        assert!(
            !accepted.versions.contains(&1),
            "{change}-accepted is not version 2 only"
        );
    }
    let frozen = find("v1-frozen-allowlists");
    assert_eq!(frozen.versions, [1]);
    let frozen_rules = find("v1-frozen-rules");
    assert_eq!(frozen_rules.versions, [1]);
    assert!(frozen_rules.expected.is_empty());
}

#[test]
fn tour_minimal_passes_policy_versions_1_and_2() {
    let source = include_str!("../../../tests/tour-minimal/src/lib.rs");
    for policy in [
        LessonPolicy::single_file_v1(),
        LessonPolicy::single_file_v2(),
    ] {
        let diagnostics = check(source, "src/lib.rs", &policy);
        assert_eq!(diagnostics, Vec::new(), "version {}", policy.version);
    }
}

/// tour-imp passes version 2; version 1 rejects it only for its two
/// `#[rustfmt::skip]` attributes.
#[test]
fn tour_imp_passes_version_2_and_fails_version_1_only_for_rustfmt_skip() {
    let source = include_str!("../../../tests/tour-imp/src/lib.rs");
    assert_eq!(
        check(source, "src/lib.rs", &LessonPolicy::single_file_v2()),
        Vec::new()
    );
    let diagnostics = check(source, "src/lib.rs", &LessonPolicy::single_file_v1());
    assert_eq!(diagnostics.len(), 2, "{diagnostics:#?}");
    for diagnostic in &diagnostics {
        assert_eq!(diagnostic.code, v1::NON_KRS_PROC_MACRO);
        let range = diagnostic.authored.clone().expect("authored range");
        assert_eq!(&source[range], "rustfmt::skip");
    }
}

#[test]
fn d007_is_rejected_at_the_external_derive_path() {
    let source = include_str!("fixtures/d007-external-proc-macro/source.rs");
    for policy in [
        LessonPolicy::single_file_v1(),
        LessonPolicy::single_file_v2(),
    ] {
        let diagnostics = check(source, "src/lib.rs", &policy);
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "krs::policy::non-krs-proc-macro");
        assert_eq!(diagnostics[0].authored, Some(9..25));
        assert_eq!(&source[9..25], "serde::Serialize");
    }
}

/// The two crate-root names the path-C expander appends
/// compile natively but collide (E0428) with the generated table in the
/// browser. Version 2 rejects them at the authored name; version 1 does not.
#[test]
fn registration_table_names_are_reserved_in_version_2() {
    let tour = include_str!("../../../tests/tour-minimal/src/lib.rs");
    for (extra, name) in [
        (
            "\npub static __KRS_REGISTRATIONS: u8 = 0;\n",
            "__KRS_REGISTRATIONS",
        ),
        (
            "\nfn __krs_register_descriptors() {}\n",
            "__krs_register_descriptors",
        ),
    ] {
        let source = format!("{tour}{extra}");
        assert_eq!(
            check(&source, "src/lib.rs", &LessonPolicy::single_file_v1()),
            Vec::new()
        );
        let diagnostics = check(&source, "src/lib.rs", &LessonPolicy::single_file_v2());
        assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
        assert_eq!(diagnostics[0].code, v2::RESERVED_NAME);
        let range = diagnostics[0].authored.clone().expect("authored range");
        assert_eq!(&source[range], name);
    }
}

#[test]
fn request_files_outside_the_allowlist_are_rejected_without_a_range() {
    let files = BTreeMap::from([
        ("src/lib.rs".to_owned(), "pub struct Accepted;\n".to_owned()),
        ("src/extra.rs".to_owned(), "pub struct Extra;\n".to_owned()),
    ]);
    let diagnostics = check_request(&files, &LessonPolicy::single_file_v1());
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, v1::EDITABLE_FILE);
    assert_eq!(diagnostics[0].file, "src/extra.rs");
    assert_eq!(diagnostics[0].authored, None);
    assert_eq!(diagnostics[0].class, "unmappable");
}

#[test]
fn unknown_policy_version_is_a_request_level_rejection() {
    let policy = LessonPolicy {
        version: 3,
        ..LessonPolicy::single_file_v1()
    };
    let files = BTreeMap::from([("src/lib.rs".to_owned(), String::new())]);
    for diagnostics in [
        check("", "src/lib.rs", &policy),
        check_request(&files, &policy),
    ] {
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].code, "krs::policy::unknown-version");
        assert_eq!(diagnostics[0].authored, None);
    }
}

#[test]
fn json_protocol_reports_d007() {
    let source = include_str!("fixtures/d007-external-proc-macro/source.rs");
    let request = serde_json::json!({
        "schema": 1,
        "policy": { "version": 1, "editable_files": ["src/lib.rs"], "facade_alias": "k" },
        "files": { "src/lib.rs": source },
    });
    let response: serde_json::Value =
        serde_json::from_slice(&protocol::run_json(request.to_string().as_bytes())).unwrap();
    assert_eq!(
        response,
        serde_json::json!({
            "schema": 1,
            "ok": false,
            "policy_version": 1,
            "diagnostics": [{
                "code": "krs::policy::non-krs-proc-macro",
                "message": "derive `serde::Serialize` is not a built-in derive; lessons cannot run external procedural macros",
                "file": "src/lib.rs",
                "authored": [9, 25],
                "class": "exact-authored",
            }],
        })
    );
}

#[test]
fn json_protocol_applies_version_2() {
    let source = "#[derive(Clone)]\n#[k::cell]\npub struct __KrsCell;\n";
    let request = serde_json::json!({
        "schema": 1,
        "policy": { "version": 2, "editable_files": ["src/lib.rs"], "facade_alias": "k" },
        "files": { "src/lib.rs": source },
    });
    let response: serde_json::Value =
        serde_json::from_slice(&protocol::run_json(request.to_string().as_bytes())).unwrap();
    assert_eq!(response["ok"], false);
    assert_eq!(response["policy_version"], 2);
    let observed: Vec<(String, serde_json::Value)> = response["diagnostics"]
        .as_array()
        .unwrap()
        .iter()
        .map(|diagnostic| {
            (
                diagnostic["code"].as_str().unwrap().to_owned(),
                diagnostic["authored"].clone(),
            )
        })
        .collect();
    assert_eq!(
        observed,
        [
            (v2::ATTRIBUTE_ORDER.to_owned(), serde_json::json!([0, 16])),
            (v2::RESERVED_NAME.to_owned(), serde_json::json!([39, 48])),
        ]
    );
}

#[test]
fn json_protocol_rejects_malformed_requests() {
    for request in [
        &b"not json"[..],
        br#"{"schema":2,"policy":{"version":1,"editable_files":[],"facade_alias":"k"},"files":{}}"#,
        br#"{"schema":1,"policy":{"version":1,"editable_files":[],"facade_alias":"k","rules":[]},"files":{}}"#,
    ] {
        let response: serde_json::Value =
            serde_json::from_slice(&protocol::run_json(request)).unwrap();
        assert_eq!(response["ok"], false);
        assert_eq!(response["policy_version"], serde_json::Value::Null);
        assert_eq!(response["diagnostics"][0]["code"], "krs::policy::protocol");
    }
}

/// The `#[proc_macro]` and `#[proc_macro_attribute]` functions of
/// `krs-macros`, split by kind, and the reserved (`__`-prefixed) ones.
struct KrsMacroEntries {
    attributes: Vec<String>,
    functions: Vec<String>,
    reserved: Vec<(String, bool)>,
}

/// Collects every `#[proc_macro]` and `#[proc_macro_attribute]` function of
/// `krs-macros`. A function whose name starts with `__` is facade-internal
/// and goes to `reserved` with whether it is `#[doc(hidden)]`.
fn krs_macro_entries() -> KrsMacroEntries {
    let file = syn::parse_file(include_str!("../../krs-macros/src/lib.rs"))
        .expect("krs-macros/src/lib.rs parses");
    let mut entries = KrsMacroEntries {
        attributes: Vec::new(),
        functions: Vec::new(),
        reserved: Vec::new(),
    };
    for item in file.items {
        let syn::Item::Fn(function) = item else {
            continue;
        };
        let name = function.sig.ident.to_string();
        let is_entry = function.attrs.iter().any(|attribute| {
            attribute.path().is_ident("proc_macro_attribute")
                || attribute.path().is_ident("proc_macro")
        });
        if name.starts_with("__") {
            if is_entry {
                let hidden = function.attrs.iter().any(|attribute| {
                    attribute.path().is_ident("doc")
                        && attribute
                            .parse_args::<syn::Ident>()
                            .is_ok_and(|argument| argument == "hidden")
                });
                entries.reserved.push((name, hidden));
            }
            continue;
        }
        for attribute in &function.attrs {
            if attribute.path().is_ident("proc_macro_attribute") {
                entries.attributes.push(name.clone());
            } else if attribute.path().is_ident("proc_macro") {
                entries.functions.push(name.clone());
            }
        }
    }
    entries
}

/// The latest version's entry allowlists equal the `krs-macros` entry
/// points. A new entry point needs a new policy version, because published
/// versions are frozen.
#[test]
fn krs_entry_allowlists_equal_the_krs_macros_entry_points() {
    let entries = krs_macro_entries();
    assert_eq!(entries.attributes, v2::ATTRIBUTE_ENTRIES);
    assert_eq!(entries.functions, v2::FUNCTION_ENTRIES);
}

/// Version 1 is frozen: its tables equal the values it was published with
/// (commit 8f1c64c). Version 2 reuses every version 1 table except the
/// allowlists it adds.
#[test]
fn version_1_tables_are_frozen_and_reused_by_version_2() {
    let frozen = format!(
        "{:?}",
        (
            v1::CODES,
            v1::ATTRIBUTE_ENTRIES,
            v1::FUNCTION_ENTRIES,
            (
                v1::ENUM_HELPERS,
                v1::VARIANT_HELPERS,
                v1::FIELD_HELPERS,
                v1::PARAMETER_HELPERS
            ),
            v1::INERT_ATTRIBUTES,
            v1::BUILTIN_DERIVES,
            v1::DERIVE_CRATES,
            v1::STANDARD_MACROS,
            v1::STANDARD_MACRO_CRATES,
        )
    );
    assert_eq!(
        frozen,
        concat!(
            r#"(["krs::policy::editable-file", "krs::policy::parse", "krs::policy::out-of-line-module", "krs::policy::path-attribute", "krs::policy::extern-crate", "krs::policy::include", "krs::policy::env", "krs::policy::macro-definition", "krs::policy::non-krs-proc-macro", "krs::policy::krs-import", "krs::policy::reserved-facade-item", "krs::policy::cfg", "krs::policy::krs-item-scope"], "#,
            r#"["sort", "symbol", "constructor", "function", "constructors", "token", "bracket", "subsort", "strict", "seqstrict", "configuration", "cell", "init", "rule", "equation", "simplification", "claim", "alias", "context_alias", "priority", "requires", "exists", "ensures"], "#,
            r#"["sorts", "rules", "term", "id", "bytes", "anonymous", "or_bool", "fragment", "k", "map", "cells", "precedence", "associativity"], "#,
            r#"(["precedence"], ["syntax", "format", "strict", "seqstrict", "alias"], ["cell"], ["config_var"]), "#,
            r#"["doc", "allow", "warn", "deny", "forbid", "expect", "must_use", "inline", "derive", "non_exhaustive", "repr"], "#,
            r#"[("Clone", "clone"), ("Copy", "marker"), ("Debug", "fmt"), ("Default", "default"), ("Eq", "cmp"), ("Hash", "hash"), ("Ord", "cmp"), ("PartialEq", "cmp"), ("PartialOrd", "cmp")], "#,
            r#"["core", "std"], "#,
            r#"["assert", "assert_eq", "assert_ne", "debug_assert", "debug_assert_eq", "debug_assert_ne", "format", "format_args", "matches", "panic", "todo", "unimplemented", "unreachable", "vec", "write", "writeln", "concat", "stringify"], "#,
            r#"["core", "std", "alloc"])"#,
        )
    );
    assert_eq!(&v2::CODES[..v1::CODES.len()], v1::CODES);
    assert_eq!(
        &v2::CODES[v1::CODES.len()..],
        [v2::ATTRIBUTE_ORDER, v2::RESERVED_NAME]
    );
    assert_eq!(v2::INERT_ATTRIBUTES, v1::INERT_ATTRIBUTES);
    assert_eq!(v2::BUILTIN_DERIVES, v1::BUILTIN_DERIVES);
    assert_eq!(v2::STANDARD_MACROS, v1::STANDARD_MACROS);
}

/// The attributes version 2 treats as order-sensitive are exactly the
/// accepted attributes that the path-C expander does not skip as inert when
/// it chooses the attribute to expand (`krs_syntax::surface`).
#[test]
fn order_sensitive_attributes_match_the_expanders_inert_set() {
    let expander_inert = krs_syntax::surface::INERT_ATTRIBUTES;
    let expander_tools = krs_syntax::surface::TOOL_ATTRIBUTES;
    let policy_single: Vec<&str> = v2::INERT_ATTRIBUTES
        .iter()
        .chain(v2::VARIANT_ATTRIBUTES)
        .copied()
        .collect();
    let not_skipped: Vec<&str> = policy_single
        .iter()
        .copied()
        .filter(|name| !expander_inert.iter().any(|inert| inert == name))
        .collect();
    // `default` is accepted on variants only, never on an item, so it never
    // precedes a KRS attribute.
    assert_eq!(not_skipped, ["derive", "default"]);
    assert_eq!(v2::ORDER_SENSITIVE_ATTRIBUTES, ["derive"]);
    for (tool, _) in v2::TOOL_ATTRIBUTES {
        assert!(
            expander_tools.contains(tool),
            "the expander does not skip `{tool}::` attributes"
        );
    }
}

#[test]
fn reserved_krs_macros_entry_points_are_hidden_and_rejected() {
    for (name, hidden) in krs_macro_entries().reserved {
        assert!(
            hidden,
            "reserved entry point `{name}` must be #[doc(hidden)]"
        );
        for (source, policy) in [
            format!("k::{name}! {{}}\n"),
            format!("#[k::{name}]\npub struct S;\n"),
        ]
        .into_iter()
        .flat_map(|source| {
            [
                (source.clone(), LessonPolicy::single_file_v1()),
                (source, LessonPolicy::single_file_v2()),
            ]
        }) {
            let diagnostics = check(&source, "src/lib.rs", &policy);
            assert!(
                diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.code == v1::RESERVED_FACADE_ITEM),
                "`{name}` is not rejected as a reserved facade item in {source:?}: {diagnostics:?}"
            );
        }
    }
}

#[test]
fn krs_facade_reexports_every_entry_point_under_its_own_name() {
    let file =
        syn::parse_file(include_str!("../../krs/src/lib.rs")).expect("krs/src/lib.rs parses");
    let mut reexported = BTreeSet::new();
    for item in file.items {
        let syn::Item::Use(item) = item else { continue };
        let syn::UseTree::Path(path) = &item.tree else {
            continue;
        };
        if path.ident != "krs_macros" {
            continue;
        }
        let syn::UseTree::Group(group) = &*path.tree else {
            panic!("krs re-exports krs_macros through one group");
        };
        for tree in &group.items {
            let syn::UseTree::Name(name) = tree else {
                panic!("krs re-exports krs_macros entries without renaming");
            };
            reexported.insert(name.ident.to_string());
        }
    }
    let expected: BTreeSet<String> = v2::ATTRIBUTE_ENTRIES
        .iter()
        .chain(v2::FUNCTION_ENTRIES)
        .map(|name| (*name).to_owned())
        .collect();
    assert_eq!(reexported, expected);
}

#[test]
fn helper_allowlists_name_helpers_the_renderers_consume() {
    let enum_constructor = include_str!("../../krs-syntax/src/enum_constructor.rs");
    for helper in v2::ENUM_HELPERS.iter().chain(v2::VARIANT_HELPERS) {
        assert!(
            enum_constructor.contains(&format!("is_helper_named(&attribute, \"{helper}\")")),
            "enum_constructor.rs no longer consumes `{helper}`"
        );
    }
    let configuration = include_str!("../../krs-syntax/src/configuration.rs");
    for helper in v2::FIELD_HELPERS {
        assert!(
            configuration.contains(&format!("segment.ident == \"{helper}\"")),
            "configuration.rs no longer consumes `{helper}`"
        );
    }
    let initializer = include_str!("../../krs-syntax/src/initializer.rs");
    for helper in v2::PARAMETER_HELPERS {
        assert!(
            initializer.contains(&format!("segment.ident == \"{helper}\"")),
            "initializer.rs no longer consumes `{helper}`"
        );
    }
}
