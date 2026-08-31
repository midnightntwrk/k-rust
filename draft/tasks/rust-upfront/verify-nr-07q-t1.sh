#!/usr/bin/env bash
set -euo pipefail

readonly KRS_REVISION=be5f8449854567f198e841d2a96fbe188cfa96ac
readonly K_RUST_REVISION=c41caa8bede96e279e0b058577dce504e4144f65
readonly RUST_VERSION=1.98.0
readonly PROTECTED_SHA256=dcc35b3bd0c01793c50d3d8096283bd650f591a529d036c79e703ac50fa6d0ec

SCRIPT_DIRECTORY="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly SCRIPT_DIRECTORY
REPOSITORY_ROOT="$(cd -- "$SCRIPT_DIRECTORY/../../.." && pwd -P)"
readonly REPOSITORY_ROOT
KRS_SOURCE="$(cd -- "${KINK_NR07Q_KRS_SOURCE:-$REPOSITORY_ROOT/../krs}" && pwd -P)"
readonly KRS_SOURCE
K_RUST_SOURCE="$(cd -- "${KINK_NR07Q_K_RUST_SOURCE:-$REPOSITORY_ROOT/../inspirations/midnightntwrk/k-rust-krs-main}" && pwd -P)"
readonly K_RUST_SOURCE
readonly SELECTED_SURFACE_MANIFEST="$REPOSITORY_ROOT/crates/kink-native/tests/fixtures/nr_07q_selected_surface.toml"
readonly EXECUTION_MANIFEST="$REPOSITORY_ROOT/crates/kink-native/tests/fixtures/nr_07q_t1_execution.toml"
SCRATCH_PARENT="$(cd -- "${KINK_NR07Q_TMPDIR:-/var/tmp}" && pwd -P)"
readonly SCRATCH_PARENT

case "$SCRATCH_PARENT" in
    /*) ;;
    *)
        echo "NR-07Q-T1 scratch parent is not absolute: $SCRATCH_PARENT" >&2
        exit 1
        ;;
esac
test -d "$SCRATCH_PARENT"
test -w "$SCRATCH_PARENT"

verify_protected_artifact() {
    local artifact actual
    artifact="$REPOSITORY_ROOT/investigations/k-rust-target/k-rust-agent-requests.toml"
    actual="$(sha256sum -- "$artifact")"
    actual="${actual%% *}"
    if [[ "$actual" != "$PROTECTED_SHA256" ]]; then
        echo "NR-07Q-T1 protected artifact SHA-256 is $actual, expected $PROTECTED_SHA256." >&2
        return 1
    fi
    echo "PASS protected artifact SHA-256 $actual"
}

verify_protected_artifact

command -v agent-self >/dev/null
agent-self

if pgrep -x cargo >/dev/null || pgrep -x rustc >/dev/null; then
    echo "NR-07Q-T1 refuses to overlap another cargo or rustc process." >&2
    ps -eo pid=,comm=,args= | awk '$2 == "cargo" || $2 == "rustc"'
    exit 1
fi

git -c safe.directory="$KRS_SOURCE" -C "$KRS_SOURCE" cat-file -e "$KRS_REVISION^{commit}"
git -c safe.directory="$K_RUST_SOURCE" -C "$K_RUST_SOURCE" cat-file -e "$K_RUST_REVISION^{commit}"

SCRATCH="$(mktemp -d -- "$SCRATCH_PARENT/kink-nr07q-t1.XXXXXX")"
readonly SCRATCH
readonly EXPECTED_PREFIX="$SCRATCH_PARENT/kink-nr07q-t1."
case "$SCRATCH" in
    "$EXPECTED_PREFIX"*) ;;
    *)
        echo "mktemp returned an unexpected NR-07Q-T1 root: $SCRATCH" >&2
        exit 1
        ;;
esac

cleanup() {
    case "$SCRATCH" in
        "$EXPECTED_PREFIX"*) rm -rf -- "$SCRATCH" ;;
        *) echo "refusing to remove unexpected NR-07Q-T1 root: $SCRATCH" >&2 ;;
    esac
}
trap cleanup EXIT

readonly EXERCISE_RECORDS="$SCRATCH/exercises.tsv"
python3 - "$SELECTED_SURFACE_MANIFEST" "$EXECUTION_MANIFEST" >"$EXERCISE_RECORDS" <<'PY'
import re
import sys
import tomllib
from pathlib import Path

selected_path = Path(sys.argv[1])
execution_path = Path(sys.argv[2])
selected = tomllib.loads(selected_path.read_text(encoding="utf-8"))
execution = tomllib.loads(execution_path.read_text(encoding="utf-8"))

KRS_REVISION = "be5f8449854567f198e841d2a96fbe188cfa96ac"
K_RUST_REVISION = "c41caa8bede96e279e0b058577dce504e4144f65"
CASE_IDS = ["application", "literal", "reference"]
STAGES = ["syntax_parse", "semantic_ir", "definition_ir", "native_adaptation"]
PACKAGES = ["krs-ir", "krs-k-rust", "krs-syntax"]
TARGET_KINDS = ["integration", "lib"]
OUTCOMES = ["success"]
SAFE_FIELD = re.compile(r"^[A-Za-z0-9_./:#-]+$")

def exact_keys(value, expected, context):
    actual = set(value)
    wanted = set(expected)
    if actual != wanted:
        raise SystemExit(f"{context} keys are not closed: {sorted(actual)} != {sorted(wanted)}")

exact_keys(
    execution,
    [
        "closure",
        "component_chain_continuous",
        "exercise",
        "k_rust_revision",
        "krs_qual_001_closed",
        "krs_revision",
        "nr_07a_required_status",
        "nr_07i_unblocked",
        "production_authority",
        "provenance_status",
        "qualification_authority",
        "rust_version",
        "schema_version",
        "selected_surface_manifest",
        "status",
        "tranche_id",
        "z3_version",
    ],
    "execution manifest",
)
if execution["schema_version"] != 1:
    raise SystemExit("unknown NR-07Q-T1 schema version")
if execution["tranche_id"] != "k-in-k2/nr-07q-t1-expression-component-evidence/v1":
    raise SystemExit("unexpected NR-07Q-T1 tranche ID")
if execution["status"] not in [
    "implemented-unrun-no-qualification-authority",
    "passed-component-evidence-no-qualification-authority",
]:
    raise SystemExit("NR-07Q-T1 status crossed its non-authoritative boundary")
if execution["selected_surface_manifest"] != "crates/kink-native/tests/fixtures/nr_07q_selected_surface.toml":
    raise SystemExit("NR-07Q-T1 selected-surface manifest path drifted")
if execution["krs_revision"] != KRS_REVISION or selected["krs_revision"] != KRS_REVISION:
    raise SystemExit("NR-07Q-T1 KRS revision drifted")
if execution["k_rust_revision"] != K_RUST_REVISION or selected["k_rust_revision"] != K_RUST_REVISION:
    raise SystemExit("NR-07Q-T1 k-rust revision drifted")
if execution["rust_version"] != "1.98.0":
    raise SystemExit("NR-07Q-T1 native/frontend Rust version drifted")
if execution["z3_version"] != "4.12.5":
    raise SystemExit("NR-07Q-T1 Z3 version drifted")
if execution["nr_07a_required_status"] != "accepted-fixture-only-positive-transport":
    raise SystemExit("NR-07Q-T1 requires the accepted NR-07A runtime gate")
if selected["manifest_id"] != "k-in-k2/nr-07q-selected-surface/v1" or selected["status"] != "setup-only-disabled":
    raise SystemExit("NR-07Q-T1 selected-surface identity or setup status drifted")
if selected["krs_descriptor_protocol"] != 35 or selected["krs_ir_schema"] != 27:
    raise SystemExit("NR-07Q-T1 KRS protocol or IR schema drifted")
if selected["nr_07a_observed_status"] != "accepted-fixture-only-positive-transport":
    raise SystemExit("the selected-surface manifest does not record accepted NR-07A")
if execution["provenance_status"] != "sidecar-only-missing-bridge":
    raise SystemExit("NR-07Q-T1 must retain SidecarOnlyMissingBridge")
for key in [
    "component_chain_continuous",
    "qualification_authority",
    "krs_qual_001_closed",
    "production_authority",
    "nr_07i_unblocked",
]:
    if execution[key] is not False:
        raise SystemExit(f"NR-07Q-T1 authority boundary {key} must remain false")
if selected["qualification_authority"] is not False or selected["production_authority"] is not False:
    raise SystemExit("the selected-surface manifest has unexpected authority")

closure = execution["closure"]
exact_keys(closure, ["case_ids", "outcomes", "packages", "stages", "target_kinds"], "closure")
for key, expected in [
    ("case_ids", CASE_IDS),
    ("stages", STAGES),
    ("packages", PACKAGES),
    ("target_kinds", TARGET_KINDS),
    ("outcomes", OUTCOMES),
]:
    if closure[key] != expected:
        raise SystemExit(f"closure.{key} drifted from the compiled catalog")

selected_cases = {case["id"]: case for case in selected["case"]}
for case_id in CASE_IDS:
    case = selected_cases.get(case_id)
    if case is None:
        raise SystemExit(f"selected-surface case {case_id!r} is absent")
    if case["enabled"] is not False or case["disposition"] != "selected" or case["authority"] != "none":
        raise SystemExit(f"selected-surface case {case_id!r} crossed its disabled authority boundary")
    if case["expected_stage"] != "native_adaptation" or case["expected_outcome"] != "success":
        raise SystemExit(f"selected-surface case {case_id!r} no longer ends at native_adaptation success")

exercise_keys = [
    "case_ids",
    "evidence",
    "expected_outcome",
    "id",
    "package",
    "stage",
    "target",
    "target_kind",
    "test_name",
]
exercises = execution["exercise"]
if not exercises:
    raise SystemExit("NR-07Q-T1 has no exercises")
prior_id = None
seen_ids = set()
covered_stages = set()
covered_evidence = {case_id: set() for case_id in CASE_IDS}
for exercise in exercises:
    exact_keys(exercise, exercise_keys, "exercise")
    exercise_id = exercise["id"]
    if prior_id is not None and exercise_id <= prior_id:
        raise SystemExit("NR-07Q-T1 exercises are not strictly sorted")
    prior_id = exercise_id
    if exercise_id in seen_ids:
        raise SystemExit(f"duplicate exercise {exercise_id!r}")
    seen_ids.add(exercise_id)
    for key in ["id", "evidence", "package", "stage", "target", "target_kind", "test_name"]:
        value = exercise[key]
        if not isinstance(value, str) or not SAFE_FIELD.fullmatch(value):
            raise SystemExit(f"unsafe exercise field {key}={value!r}")
    if exercise["stage"] not in STAGES:
        raise SystemExit(f"unknown stage {exercise['stage']!r}")
    if exercise["package"] not in PACKAGES:
        raise SystemExit(f"unknown package {exercise['package']!r}")
    if exercise["target_kind"] not in TARGET_KINDS:
        raise SystemExit(f"unknown target kind {exercise['target_kind']!r}")
    if exercise["expected_outcome"] != "success":
        raise SystemExit("NR-07Q-T1 admits only positive component exercises")
    if exercise["target_kind"] == "integration" and exercise["target"] == "-":
        raise SystemExit("integration exercise requires an explicit target")
    if exercise["target_kind"] == "lib" and exercise["target"] != "-":
        raise SystemExit("lib exercise target must be the closed '-' sentinel")
    if not exercise["case_ids"] or exercise["case_ids"] != sorted(set(exercise["case_ids"])):
        raise SystemExit(f"exercise {exercise_id!r} case IDs must be sorted and unique")
    for case_id in exercise["case_ids"]:
        if case_id not in CASE_IDS:
            raise SystemExit(f"exercise {exercise_id!r} names unknown case {case_id!r}")
        if exercise["evidence"] not in selected_cases[case_id]["evidence"]:
            raise SystemExit(f"exercise {exercise_id!r} is not evidence for case {case_id!r}")
        covered_evidence[case_id].add(exercise["evidence"])
    evidence_path, separator, evidence_test = exercise["evidence"].partition("#")
    if separator != "#" or evidence_test != exercise["test_name"].removeprefix("tests::"):
        raise SystemExit(f"exercise {exercise_id!r} evidence/test mismatch")
    covered_stages.add(exercise["stage"])

if covered_stages != set(STAGES):
    raise SystemExit("NR-07Q-T1 does not cover its exact stage catalog")
for case_id in CASE_IDS:
    expected = set(selected_cases[case_id]["evidence"])
    if covered_evidence[case_id] != expected:
        raise SystemExit(f"NR-07Q-T1 evidence coverage for {case_id!r} is incomplete")

for exercise in exercises:
    fields = [
        exercise["id"],
        exercise["stage"],
        exercise["package"],
        exercise["target_kind"],
        exercise["target"],
        exercise["test_name"],
        exercise["evidence"],
        ",".join(exercise["case_ids"]),
    ]
    print("\t".join(fields))
PY

readonly CLEAN_ROOT="$SCRATCH/starstream-fv"
readonly CLEAN_KRS="$CLEAN_ROOT/krs"
readonly CLEAN_K_RUST="$CLEAN_ROOT/inspirations/midnightntwrk/k-rust-krs-main"
readonly KRS_TARGET="$SCRATCH/krs-target-z3"

mkdir -p -- "$(dirname -- "$CLEAN_K_RUST")"
git -c safe.directory="$KRS_SOURCE" clone --shared --no-checkout -- "$KRS_SOURCE" "$CLEAN_KRS"
git -c safe.directory="$CLEAN_KRS" -C "$CLEAN_KRS" checkout --detach "$KRS_REVISION"
git -c safe.directory="$K_RUST_SOURCE" clone --shared --no-checkout -- "$K_RUST_SOURCE" "$CLEAN_K_RUST"
git -c safe.directory="$CLEAN_K_RUST" -C "$CLEAN_K_RUST" checkout --detach "$K_RUST_REVISION"

test -z "$(git -c safe.directory="$CLEAN_KRS" -C "$CLEAN_KRS" status --porcelain)"
test -z "$(git -c safe.directory="$CLEAN_K_RUST" -C "$CLEAN_K_RUST" status --porcelain)"

Z3_LIBRARY_DIRECTORY="${KINK_NR07Q_Z3_LIB:-}"
if [[ -z "$Z3_LIBRARY_DIRECTORY" ]]; then
    for candidate in /nix/store/*-z3-4.12.5-lib/lib; do
        if [[ -f "$candidate/libz3.so" ]]; then
            Z3_LIBRARY_DIRECTORY="$candidate"
            break
        fi
    done
fi
if [[ -z "$Z3_LIBRARY_DIRECTORY" ]]; then
    echo "NR-07Q-T1 could not locate the pinned Z3 4.12.5 library directory." >&2
    exit 1
fi
Z3_LIBRARY_DIRECTORY="$(cd -- "$Z3_LIBRARY_DIRECTORY" && pwd -P)"
readonly Z3_LIBRARY_DIRECTORY
test -f "$Z3_LIBRARY_DIRECTORY/libz3.so"
test "$(z3 --version)" = "Z3 version 4.12.5 - 64 bit"
rustc_identity="$(rustc +stable --version --verbose)"
readonly rustc_identity
if [[ "$(awk '$1 == "release:" { print $2 }' <<<"$rustc_identity")" != "$RUST_VERSION" ]]; then
    echo "NR-07Q-T1 requires exact stable Rust $RUST_VERSION." >&2
    exit 1
fi

run_pinned_cargo() {
    CARGO_BUILD_JOBS=1 \
    CARGO_INCREMENTAL=0 \
    CARGO_TARGET_DIR="$KRS_TARGET" \
    LIBRARY_PATH="$Z3_LIBRARY_DIRECTORY${LIBRARY_PATH:+:$LIBRARY_PATH}" \
    LD_LIBRARY_PATH="$Z3_LIBRARY_DIRECTORY${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
        cargo "$@"
}

while IFS=$'\t' read -r exercise_id stage package target_kind target test_name evidence case_ids; do
    echo "RUN NR-07Q-T1 $exercise_id stage=$stage cases=$case_ids evidence=$evidence"
    evidence_path="${evidence%%#*}"
    evidence_test="${evidence#*#}"
    test -f "$CLEAN_KRS/$evidence_path"
    rg -Fq "fn $evidence_test(" "$CLEAN_KRS/$evidence_path"
    common=(
        +stable test
        --locked
        --manifest-path "$CLEAN_KRS/Cargo.toml"
        -p "$package"
    )
    case "$target_kind" in
        integration)
            target_arguments=(--test "$target")
            ;;
        lib)
            target_arguments=(--lib)
            ;;
        *)
            echo "NR-07Q-T1 admitted unknown target kind $target_kind after validation." >&2
            exit 1
            ;;
    esac
    listed_tests="$(run_pinned_cargo "${common[@]}" "${target_arguments[@]}" -- --list --format terse)"
    matching_test_count="$(awk -v wanted="$test_name: test" '$0 == wanted { count += 1 } END { print count + 0 }' <<<"$listed_tests")"
    if [[ "$matching_test_count" != 1 ]]; then
        echo "NR-07Q-T1 expected exactly one registered test named $test_name, found $matching_test_count." >&2
        exit 1
    fi
    run_pinned_cargo "${common[@]}" "${target_arguments[@]}" -- --exact "$test_name"
done <"$EXERCISE_RECORDS"

echo "PASS NR-07Q-T1 expression component evidence at exact pins."
echo "NO AUTHORITY: component continuity, full NR-07Q, KRS-QUAL-001, provenance, production, and NR-07I remain unaccepted."
verify_protected_artifact
