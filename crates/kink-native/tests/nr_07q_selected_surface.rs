//! NR-07Q-S selected-surface qualification scaffold.
//!
//! This target only validates the closed setup manifest. Every qualification
//! case remains disabled until NR-07A is accepted and NR-07Q owns execution.

use std::collections::BTreeSet;

use toml::{Table, Value};

const MANIFEST: &str = include_str!("fixtures/nr_07q_selected_surface.toml");
const KRS_REVISION: &str = "be5f8449854567f198e841d2a96fbe188cfa96ac";
const K_RUST_REVISION: &str = "c41caa8bede96e279e0b058577dce504e4144f65";

const DISPOSITIONS: &[&str] = &["missing_gap", "selected", "unsupported"];
const SYNTAX_FORMS: &[&str] = &[
    "alias_rule",
    "anonymous",
    "application",
    "associativity_declaration",
    "bytes_token",
    "cell",
    "claim_rule",
    "configuration_initializer",
    "context_alias",
    "equation_rule",
    "id_token",
    "k_sequence",
    "list",
    "literal",
    "map",
    "module_import",
    "or_bool",
    "precedence_declaration",
    "production_declaration",
    "reference",
    "set",
    "simplification_rule",
    "sort_declaration",
    "strictness_attribute",
    "subsort_declaration",
    "transition_rule",
    "unsupported_host_expression",
    "whole_configuration_rule",
    "wildcard",
];
const SEMANTIC_IR_FORMS: &[&str] = &[
    "application",
    "associativity",
    "cell",
    "configuration",
    "context_alias",
    "k_sequence",
    "list",
    "map",
    "module",
    "precedence",
    "production",
    "rewrite",
    "rule",
    "set",
    "sort",
    "subsort",
    "token",
    "variable",
];
const DEFINITION_IR_FORMS: &[&str] = &[
    "application",
    "associativity",
    "cell",
    "configuration",
    "context_alias",
    "k_sequence",
    "list",
    "map",
    "module",
    "precedence",
    "production",
    "rewrite",
    "rule",
    "set",
    "subsort",
    "syntax_sort",
    "token",
    "variable",
];
const NATIVE_ROLES: &[&str] = &[
    "claim_binder",
    "claim_binder_name",
    "claim_binder_sort",
    "claim_circularity",
    "claim_modality",
    "configuration_cell",
    "configuration_initializer",
    "configuration_rule_cell",
    "configuration_rule_frame",
    "context_alias_cell",
    "context_alias_frame",
    "context_alias_here",
    "context_alias_name",
    "ensures",
    "module",
    "production_attribute",
    "production_item",
    "requires",
    "sentence",
    "strictness_context_alias",
    "strictness_field",
    "strictness_result",
    "term",
];
const STAGES: &[&str] = &[
    "syntax_parse",
    "descriptor_collection",
    "semantic_ir",
    "definition_ir",
    "origin_mapping",
    "native_adaptation",
    "native_preparation",
    "frontend_compile",
    "kore_reparse",
    "backend_execution",
];
const OUTCOMES: &[&str] = &["blocked", "structured_failure", "success"];
const HOOK_CATALOG: &[&str] = &[
    "krypto_bn128_ate",
    "krypto_bn128_add",
    "krypto_bn128_g2_valid",
    "krypto_bn128_mul",
    "krypto_bn128_valid",
    "krypto_ecdsa_recover",
    "krypto_keccak256_raw",
    "krypto_ripemd160_raw",
    "krypto_sha256_raw",
];

#[test]
fn qualification_cases_are_closed_table_driven_and_disabled() {
    let manifest = MANIFEST
        .parse::<Table>()
        .expect("the NR-07Q selected-surface manifest must parse as TOML");
    require_exact_keys(
        &manifest,
        &[
            "case",
            "closure",
            "k_rust_revision",
            "krs_descriptor_protocol",
            "krs_ir_schema",
            "krs_revision",
            "manifest_id",
            "nr_07a_observed_status",
            "nr_07a_required_status",
            "production_authority",
            "provenance_status",
            "qualification_authority",
            "schema_version",
            "selection",
            "status",
        ],
        "manifest",
    );
    assert_eq!(integer(&manifest, "schema_version"), 1);
    assert_eq!(integer(&manifest, "krs_descriptor_protocol"), 35);
    assert_eq!(integer(&manifest, "krs_ir_schema"), 27);
    assert_eq!(
        string(&manifest, "manifest_id"),
        "k-in-k2/nr-07q-selected-surface/v1"
    );
    assert_eq!(string(&manifest, "krs_revision"), KRS_REVISION);
    assert_eq!(string(&manifest, "k_rust_revision"), K_RUST_REVISION);
    assert_eq!(string(&manifest, "status"), "setup-only-disabled");
    assert_eq!(
        string(&manifest, "nr_07a_required_status"),
        "accepted-current-pin-runtime-gate"
    );
    assert_eq!(
        string(&manifest, "nr_07a_observed_status"),
        "accepted-fixture-only-positive-transport"
    );
    assert_eq!(
        string(&manifest, "provenance_status"),
        "sidecar-only-missing-bridge"
    );
    assert!(!boolean(&manifest, "qualification_authority"));
    assert!(!boolean(&manifest, "production_authority"));

    let closure = table(&manifest, "closure");
    require_exact_keys(
        closure,
        &[
            "definition_ir_forms",
            "dispositions",
            "native_roles",
            "outcomes",
            "semantic_ir_forms",
            "stages",
            "syntax_forms",
        ],
        "closure",
    );
    require_exact_closed_array(closure, "dispositions", DISPOSITIONS);
    require_exact_closed_array(closure, "syntax_forms", SYNTAX_FORMS);
    require_exact_closed_array(closure, "semantic_ir_forms", SEMANTIC_IR_FORMS);
    require_exact_closed_array(closure, "definition_ir_forms", DEFINITION_IR_FORMS);
    require_exact_closed_array(closure, "native_roles", NATIVE_ROLES);
    require_exact_closed_array(closure, "stages", STAGES);
    require_exact_closed_array(closure, "outcomes", OUTCOMES);

    let selection = table(&manifest, "selection");
    require_exact_keys(
        selection,
        &[
            "hook_catalog",
            "hook_policy",
            "selected_hooks",
            "selected_rule_kinds",
            "unselected_rule_kinds",
        ],
        "selection",
    );
    assert_eq!(
        string_array(selection, "selected_rule_kinds"),
        ["claim", "transition"]
    );
    assert_eq!(
        string_array(selection, "unselected_rule_kinds"),
        ["alias", "equation", "simplification"]
    );
    assert!(string_array(selection, "selected_hooks").is_empty());
    require_exact_closed_array(selection, "hook_catalog", HOOK_CATALOG);
    assert!(!string(selection, "hook_policy").is_empty());

    let cases = array(&manifest, "case");
    assert!(!cases.is_empty(), "the selected surface must not be empty");
    let mut prior_id: Option<&str> = None;
    let mut ids = BTreeSet::new();
    let mut covered_dispositions = BTreeSet::new();
    let mut covered_syntax_forms = BTreeSet::new();
    let mut covered_semantic_ir_forms = BTreeSet::new();
    let mut covered_definition_ir_forms = BTreeSet::new();
    let mut covered_native_roles = BTreeSet::new();
    let mut covered_stages = BTreeSet::new();
    let mut covered_outcomes = BTreeSet::new();
    for value in cases {
        let case = value
            .as_table()
            .expect("each qualification case must be a TOML table");
        validate_case(case, &mut prior_id, &mut ids);
        covered_dispositions.insert(string(case, "disposition"));
        covered_syntax_forms.insert(string(case, "syntax_form"));
        covered_semantic_ir_forms.extend(string_array(case, "semantic_ir_forms"));
        covered_definition_ir_forms.extend(string_array(case, "definition_ir_forms"));
        covered_native_roles.extend(string_array(case, "native_roles"));
        covered_stages.insert(string(case, "expected_stage"));
        covered_outcomes.insert(string(case, "expected_outcome"));
        if boolean(case, "enabled") {
            dispatch_qualification_case(case);
        }
    }
    require_exact_coverage(&covered_dispositions, DISPOSITIONS, "dispositions");
    require_exact_coverage(&covered_syntax_forms, SYNTAX_FORMS, "syntax forms");
    require_exact_coverage(
        &covered_semantic_ir_forms,
        SEMANTIC_IR_FORMS,
        "semantic IR forms",
    );
    require_exact_coverage(
        &covered_definition_ir_forms,
        DEFINITION_IR_FORMS,
        "Definition IR forms",
    );
    require_exact_coverage(&covered_native_roles, NATIVE_ROLES, "native roles");
    require_exact_coverage(&covered_stages, STAGES, "stages");
    require_exact_coverage(&covered_outcomes, OUTCOMES, "outcomes");
}

fn validate_case<'a>(case: &'a Table, prior_id: &mut Option<&'a str>, ids: &mut BTreeSet<&'a str>) {
    require_exact_keys(
        case,
        &[
            "authority",
            "definition_ir_forms",
            "disposition",
            "enabled",
            "evidence",
            "expected_error",
            "expected_outcome",
            "expected_stage",
            "gap_id",
            "id",
            "native_roles",
            "semantic_ir_forms",
            "syntax_form",
        ],
        "case",
    );
    let id = string(case, "id");
    assert!(ids.insert(id), "duplicate qualification case {id:?}");
    if let Some(prior) = prior_id {
        assert!(
            *prior < id,
            "qualification cases must be sorted: {prior:?} precedes {id:?}"
        );
    }
    *prior_id = Some(id);
    assert!(!boolean(case, "enabled"), "case {id:?} must be disabled");
    assert_closed_value(case, "disposition", DISPOSITIONS);
    assert_closed_value(case, "syntax_form", SYNTAX_FORMS);
    assert_closed_array(case, "semantic_ir_forms", SEMANTIC_IR_FORMS);
    assert_closed_array(case, "definition_ir_forms", DEFINITION_IR_FORMS);
    assert_closed_array(case, "native_roles", NATIVE_ROLES);
    assert_closed_value(case, "expected_stage", STAGES);
    assert_closed_value(case, "expected_outcome", OUTCOMES);
    assert_eq!(string(case, "authority"), "none");
    assert!(
        !string_array(case, "evidence").is_empty(),
        "case {id:?} must pin tracked cff5e10 evidence"
    );

    match string(case, "disposition") {
        "selected" => {
            assert!(
                string(case, "gap_id").is_empty(),
                "selected case {id:?} cannot name a gap"
            );
            assert!(
                !string_array(case, "semantic_ir_forms").is_empty(),
                "selected case {id:?} must name its semantic IR"
            );
            assert!(
                !string_array(case, "definition_ir_forms").is_empty(),
                "selected case {id:?} must name its Definition IR"
            );
            assert!(
                !string_array(case, "native_roles").is_empty(),
                "selected case {id:?} must name applicable OriginMapping roles"
            );
        }
        "missing_gap" | "unsupported" => {
            assert!(
                !string(case, "gap_id").is_empty(),
                "non-selected case {id:?} must name its gap"
            );
            assert_ne!(
                string(case, "expected_outcome"),
                "success",
                "non-selected case {id:?} cannot expect success"
            );
            assert!(
                !string(case, "expected_error").is_empty(),
                "non-selected case {id:?} must name its structured stop"
            );
        }
        unknown => panic!("closed disposition parser admitted {unknown:?}"),
    }
}

fn dispatch_qualification_case(case: &Table) -> ! {
    let id = string(case, "id");
    let stage = string(case, "expected_stage");
    match stage {
        "syntax_parse"
        | "descriptor_collection"
        | "semantic_ir"
        | "definition_ir"
        | "origin_mapping"
        | "native_adaptation"
        | "native_preparation"
        | "frontend_compile"
        | "kore_reparse"
        | "backend_execution" => {
            panic!("case {id:?} was enabled before NR-07Q supplied its {stage:?} executor")
        }
        unknown => panic!("unknown qualification stage {unknown:?}"),
    }
}

fn require_exact_keys(table: &Table, expected: &[&str], context: &str) {
    let actual = table.keys().map(String::as_str).collect::<BTreeSet<_>>();
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(actual, expected, "{context} keys must be closed");
}

fn require_exact_closed_array(table: &Table, key: &str, expected: &[&str]) {
    assert_eq!(
        string_array(table, key),
        expected,
        "closure.{key} must equal the compiled closed catalog"
    );
}

fn assert_closed_value(table: &Table, key: &str, closed: &[&str]) {
    let value = string(table, key);
    assert!(closed.contains(&value), "unknown {key} value {value:?}");
}

fn assert_closed_array(table: &Table, key: &str, closed: &[&str]) {
    for value in string_array(table, key) {
        assert!(closed.contains(&value), "unknown {key} value {value:?}");
    }
}

fn require_exact_coverage(actual: &BTreeSet<&str>, expected: &[&str], context: &str) {
    let expected = expected.iter().copied().collect::<BTreeSet<_>>();
    assert_eq!(
        *actual, expected,
        "qualification cases must cover {context}"
    );
}

fn table<'a>(table: &'a Table, key: &str) -> &'a Table {
    table
        .get(key)
        .and_then(Value::as_table)
        .unwrap_or_else(|| panic!("{key:?} must be a table"))
}

fn array<'a>(table: &'a Table, key: &str) -> &'a [Value] {
    table
        .get(key)
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("{key:?} must be an array"))
}

fn string<'a>(table: &'a Table, key: &str) -> &'a str {
    table
        .get(key)
        .and_then(Value::as_str)
        .unwrap_or_else(|| panic!("{key:?} must be a string"))
}

fn string_array<'a>(table: &'a Table, key: &str) -> Vec<&'a str> {
    array(table, key)
        .iter()
        .map(|value| {
            value
                .as_str()
                .unwrap_or_else(|| panic!("every {key:?} item must be a string"))
        })
        .collect()
}

fn integer(table: &Table, key: &str) -> i64 {
    table
        .get(key)
        .and_then(Value::as_integer)
        .unwrap_or_else(|| panic!("{key:?} must be an integer"))
}

fn boolean(table: &Table, key: &str) -> bool {
    table
        .get(key)
        .and_then(Value::as_bool)
        .unwrap_or_else(|| panic!("{key:?} must be a Boolean"))
}
