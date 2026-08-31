#!/usr/bin/env bash
set -euo pipefail

readonly KRS_REVISION=be5f8449854567f198e841d2a96fbe188cfa96ac
readonly K_RUST_REVISION=c41caa8bede96e279e0b058577dce504e4144f65
readonly RUST_VERSION=1.98.0
readonly PROTECTED_SHA256=dcc35b3bd0c01793c50d3d8096283bd650f591a529d036c79e703ac50fa6d0ec
readonly EXPECTED_SUMMARY='PASS NR-07Q-T2 continuous cases=application,literal,reference stages=9 provenance=sidecar-only-missing-bridge authority=false'

SCRIPT_DIRECTORY="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly SCRIPT_DIRECTORY
REPOSITORY_ROOT="$(cd -- "$SCRIPT_DIRECTORY/../../.." && pwd -P)"
readonly REPOSITORY_ROOT
KRS_SOURCE="$(cd -- "${KINK_NR07Q_KRS_SOURCE:-$REPOSITORY_ROOT/../krs}" && pwd -P)"
readonly KRS_SOURCE
K_RUST_SOURCE="$(cd -- "${KINK_NR07Q_K_RUST_SOURCE:-$REPOSITORY_ROOT/../inspirations/midnightntwrk/k-rust-krs-main}" && pwd -P)"
readonly K_RUST_SOURCE
readonly SELECTED_SURFACE_MANIFEST="$REPOSITORY_ROOT/crates/kink-native/tests/fixtures/nr_07q_selected_surface.toml"
readonly EXECUTION_MANIFEST="$REPOSITORY_ROOT/crates/kink-native/tests/fixtures/nr_07q_t2_execution.toml"
readonly FIXTURE_SOURCE="$REPOSITORY_ROOT/crates/kink-native/tests/fixtures/nr_07q_t2_continuous"
SCRATCH_PARENT="$(cd -- "${KINK_NR07Q_TMPDIR:-/var/tmp}" && pwd -P)"
readonly SCRATCH_PARENT

case "$SCRATCH_PARENT" in
    /*) ;;
    *)
        echo "NR-07Q-T2 scratch parent is not absolute: $SCRATCH_PARENT" >&2
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
        echo "NR-07Q-T2 protected artifact SHA-256 is $actual, expected $PROTECTED_SHA256." >&2
        return 1
    fi
    echo "PASS protected artifact SHA-256 $actual"
}

verify_protected_artifact

command -v agent-self >/dev/null
agent-self

if pgrep -x cargo >/dev/null || pgrep -x rustc >/dev/null; then
    echo "NR-07Q-T2 refuses to overlap another cargo or rustc process." >&2
    ps -eo pid=,comm=,args= | awk '$2 == "cargo" || $2 == "rustc"'
    exit 1
fi

python3 - "$SELECTED_SURFACE_MANIFEST" "$EXECUTION_MANIFEST" "$FIXTURE_SOURCE" <<'PY'
import hashlib
import sys
import tomllib
from pathlib import Path

selected_path = Path(sys.argv[1])
execution_path = Path(sys.argv[2])
fixture = Path(sys.argv[3])
selected = tomllib.loads(selected_path.read_text(encoding="utf-8"))
execution = tomllib.loads(execution_path.read_text(encoding="utf-8"))

KRS_REVISION = "be5f8449854567f198e841d2a96fbe188cfa96ac"
K_RUST_REVISION = "c41caa8bede96e279e0b058577dce504e4144f65"
CASE_IDS = ["application", "literal", "reference"]
STAGES = [
    "syntax_parse",
    "descriptor_collection",
    "semantic_ir",
    "definition_ir",
    "origin_mapping",
    "native_adaptation",
    "native_preparation",
    "frontend_compile",
    "kore_reparse",
]
FIXTURE_FILES = ["Cargo.lock", "Cargo.toml", "src/main.rs"]

def exact_keys(value, expected, context):
    actual = set(value)
    wanted = set(expected)
    if actual != wanted:
        raise SystemExit(f"{context} keys are not closed: {sorted(actual)} != {sorted(wanted)}")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

exact_keys(
    execution,
    [
        "closure",
        "component_chain_continuous",
        "fixture_lock_sha256",
        "fixture_manifest",
        "fixture_manifest_sha256",
        "fixture_source_sha256",
        "k_rust_revision",
        "krs_qual_001_closed",
        "krs_revision",
        "nr_07a_required_status",
        "nr_07i_unblocked",
        "production_authority",
        "provenance_authority",
        "provenance_status",
        "qualification_authority",
        "raw_k_escape",
        "route",
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
    raise SystemExit("unknown NR-07Q-T2 schema version")
if execution["tranche_id"] != "k-in-k2/nr-07q-t2-continuous-expression/v1":
    raise SystemExit("unexpected NR-07Q-T2 tranche ID")
if execution["status"] not in {
    "implemented-unrun-continuous-evidence-no-qualification-authority",
    "passed-continuous-evidence-no-qualification-authority",
}:
    raise SystemExit("NR-07Q-T2 status crossed its evidence-only boundary")
if execution["selected_surface_manifest"] != "crates/kink-native/tests/fixtures/nr_07q_selected_surface.toml":
    raise SystemExit("NR-07Q-T2 selected-surface path drifted")
if execution["fixture_manifest"] != "crates/kink-native/tests/fixtures/nr_07q_t2_continuous/Cargo.toml":
    raise SystemExit("NR-07Q-T2 fixture path drifted")
if execution["krs_revision"] != KRS_REVISION or selected["krs_revision"] != KRS_REVISION:
    raise SystemExit("NR-07Q-T2 KRS revision drifted")
if execution["k_rust_revision"] != K_RUST_REVISION or selected["k_rust_revision"] != K_RUST_REVISION:
    raise SystemExit("NR-07Q-T2 k-rust revision drifted")
if execution["rust_version"] != "1.98.0" or execution["z3_version"] != "4.12.5":
    raise SystemExit("NR-07Q-T2 toolchain profile drifted")
if execution["nr_07a_required_status"] != "accepted-fixture-only-positive-transport":
    raise SystemExit("NR-07Q-T2 NR-07A prerequisite drifted")
if execution["provenance_status"] != "sidecar-only-missing-bridge":
    raise SystemExit("NR-07Q-T2 must retain SidecarOnlyMissingBridge")
if execution["component_chain_continuous"] is not True:
    raise SystemExit("NR-07Q-T2 must describe one continuous component chain")
for key in [
    "raw_k_escape",
    "qualification_authority",
    "krs_qual_001_closed",
    "provenance_authority",
    "production_authority",
    "nr_07i_unblocked",
]:
    if execution[key] is not False:
        raise SystemExit(f"NR-07Q-T2 authority boundary {key} must remain false")
if selected["status"] != "setup-only-disabled":
    raise SystemExit("the selected-surface manifest no longer has setup-only status")
if selected["qualification_authority"] is not False or selected["production_authority"] is not False:
    raise SystemExit("the selected-surface manifest has unexpected authority")

closure = execution["closure"]
exact_keys(closure, ["case_ids", "fixture_files", "outcomes", "stages"], "closure")
if closure["case_ids"] != CASE_IDS or closure["stages"] != STAGES:
    raise SystemExit("NR-07Q-T2 case or stage closure drifted")
if closure["outcomes"] != ["success"] or closure["fixture_files"] != FIXTURE_FILES:
    raise SystemExit("NR-07Q-T2 outcome or fixture-file closure drifted")

selected_cases = {case["id"]: case for case in selected["case"]}
for case_id in CASE_IDS:
    case = selected_cases.get(case_id)
    if case is None:
        raise SystemExit(f"selected case {case_id!r} is absent")
    if case["enabled"] is not False or case["disposition"] != "selected" or case["authority"] != "none":
        raise SystemExit(f"selected case {case_id!r} crossed its disabled authority boundary")

route = execution["route"]
exact_keys(route, ["artifact", "driver", "summary", "syntax"], "route")
if route["artifact"] != "and_true" or route["driver"] != "kink-nr-07q-t2-continuous":
    raise SystemExit("NR-07Q-T2 route identity drifted")
if route["syntax"] != "And { lhs: true, rhs } -> rhs" or not route["summary"]:
    raise SystemExit("NR-07Q-T2 route syntax or summary drifted")

actual_files = sorted(
    path.relative_to(fixture).as_posix()
    for path in fixture.rglob("*")
    if path.is_file()
)
if actual_files != FIXTURE_FILES:
    raise SystemExit(f"NR-07Q-T2 fixture files are not closed: {actual_files}")
for key, relative in [
    ("fixture_manifest_sha256", "Cargo.toml"),
    ("fixture_lock_sha256", "Cargo.lock"),
    ("fixture_source_sha256", "src/main.rs"),
]:
    actual = digest(fixture / relative)
    if execution[key] != actual:
        raise SystemExit(f"NR-07Q-T2 {relative} SHA-256 is {actual}, expected {execution[key]}")

manifest = tomllib.loads((fixture / "Cargo.toml").read_text(encoding="utf-8"))
exact_keys(manifest, ["dependencies", "lints", "package", "workspace"], "fixture Cargo manifest")
dependencies = manifest["dependencies"]
if set(dependencies) != {"k", "k-rust", "krs-compiler", "krs-ir", "krs-k-rust"}:
    raise SystemExit("NR-07Q-T2 dependency graph is not closed")
if dependencies["k-rust"] != {
    "version": "=0.4.0",
    "path": "../../../../../../inspirations/midnightntwrk/k-rust-krs-main/crates/k-rust",
    "default-features": False,
    "features": ["z3-inference"],
}:
    raise SystemExit("NR-07Q-T2 direct k-rust dependency drifted")
for name, crate in [("k", "krs"), ("krs-compiler", "krs-compiler"), ("krs-ir", "krs-ir"), ("krs-k-rust", "krs-k-rust")]:
    dependency = dependencies[name]
    expected = f"../../../../../../krs/crates/{crate}"
    if dependency.get("path") != expected:
        raise SystemExit(f"NR-07Q-T2 dependency {name!r} path drifted")

source = (fixture / "src/main.rs").read_text(encoding="utf-8")
for required in [
    "collect_host_descriptors_with_builtins(",
    "lower_descriptor_bundle(&bundle)",
    "lower_semantic_theory(&semantic)",
    "adapt_definition(lowered.definition())",
    "prepare_definition(adapted.definition().clone(), options.backend)",
    "compile_loaded_definition(&loaded, options)",
    "parse_kore_definition(&artifacts.definition_kore)",
    "NativeNodeRole::Term(actual)",
]:
    if required not in source:
        raise SystemExit(f"NR-07Q-T2 fixture lacks required continuous step {required!r}")
for forbidden in ["emit_k", "compile_definition(", "definition.k\""]:
    if forbidden in source:
        raise SystemExit(f"NR-07Q-T2 fixture contains forbidden raw-K or re-adaptation escape {forbidden!r}")
PY

git -c safe.directory="$KRS_SOURCE" -C "$KRS_SOURCE" cat-file -e "$KRS_REVISION^{commit}"
git -c safe.directory="$K_RUST_SOURCE" -C "$K_RUST_SOURCE" cat-file -e "$K_RUST_REVISION^{commit}"

SCRATCH="$(mktemp -d -- "$SCRATCH_PARENT/kink-nr07q-t2.XXXXXX")"
readonly SCRATCH
readonly EXPECTED_PREFIX="$SCRATCH_PARENT/kink-nr07q-t2."
case "$SCRATCH" in
    "$EXPECTED_PREFIX"*) ;;
    *)
        echo "mktemp returned an unexpected NR-07Q-T2 root: $SCRATCH" >&2
        exit 1
        ;;
esac

cleanup() {
    case "$SCRATCH" in
        "$EXPECTED_PREFIX"*) rm -rf -- "$SCRATCH" ;;
        *) echo "refusing to remove unexpected NR-07Q-T2 root: $SCRATCH" >&2 ;;
    esac
}
trap cleanup EXIT

readonly CLEAN_ROOT="$SCRATCH/starstream-fv"
readonly CLEAN_KRS="$CLEAN_ROOT/krs"
readonly CLEAN_K_RUST="$CLEAN_ROOT/inspirations/midnightntwrk/k-rust-krs-main"
readonly CLEAN_FIXTURE="$CLEAN_ROOT/k-in-k2/crates/kink-native/tests/fixtures/nr_07q_t2_continuous"
readonly CARGO_TARGET="$SCRATCH/cargo-target-z3"

mkdir -p -- "$(dirname -- "$CLEAN_K_RUST")" "$(dirname -- "$CLEAN_FIXTURE")"
git -c safe.directory="$KRS_SOURCE" clone --shared --no-checkout -- "$KRS_SOURCE" "$CLEAN_KRS"
git -c safe.directory="$CLEAN_KRS" -C "$CLEAN_KRS" checkout --detach "$KRS_REVISION"
git -c safe.directory="$K_RUST_SOURCE" clone --shared --no-checkout -- "$K_RUST_SOURCE" "$CLEAN_K_RUST"
git -c safe.directory="$CLEAN_K_RUST" -C "$CLEAN_K_RUST" checkout --detach "$K_RUST_REVISION"
cp -a -- "$FIXTURE_SOURCE" "$CLEAN_FIXTURE"

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
    echo "NR-07Q-T2 could not locate the pinned Z3 4.12.5 library directory." >&2
    exit 1
fi
Z3_LIBRARY_DIRECTORY="$(cd -- "$Z3_LIBRARY_DIRECTORY" && pwd -P)"
readonly Z3_LIBRARY_DIRECTORY
test -f "$Z3_LIBRARY_DIRECTORY/libz3.so"
test "$(z3 --version)" = "Z3 version 4.12.5 - 64 bit"

rustc_identity="$(rustc +stable --version --verbose)"
readonly rustc_identity
if [[ "$(awk '$1 == "release:" { print $2 }' <<<"$rustc_identity")" != "$RUST_VERSION" ]]; then
    echo "NR-07Q-T2 requires exact stable Rust $RUST_VERSION." >&2
    exit 1
fi

echo "RUN NR-07Q-T2 one continuous and_true artifact through nine stages"
observed_summary="$({
    CARGO_BUILD_JOBS=1 \
    CARGO_INCREMENTAL=0 \
    CARGO_TARGET_DIR="$CARGO_TARGET" \
    LIBRARY_PATH="$Z3_LIBRARY_DIRECTORY${LIBRARY_PATH:+:$LIBRARY_PATH}" \
    LD_LIBRARY_PATH="$Z3_LIBRARY_DIRECTORY${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
        cargo +stable run --locked --quiet --manifest-path "$CLEAN_FIXTURE/Cargo.toml"
} 2> >(tee /dev/stderr))"
readonly observed_summary
if [[ "$observed_summary" != "$EXPECTED_SUMMARY" ]]; then
    echo "NR-07Q-T2 summary differs: $observed_summary" >&2
    exit 1
fi

test -z "$(git -c safe.directory="$CLEAN_KRS" -C "$CLEAN_KRS" status --porcelain)"
test -z "$(git -c safe.directory="$CLEAN_K_RUST" -C "$CLEAN_K_RUST" status --porcelain)"
echo "$observed_summary"
echo "NO AUTHORITY: full NR-07Q, KRS-QUAL-001, provenance, production, and NR-07I remain unaccepted."
verify_protected_artifact
