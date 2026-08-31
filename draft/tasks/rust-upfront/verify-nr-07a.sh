#!/usr/bin/env bash
set -euo pipefail

readonly KRS_REVISION=be5f8449854567f198e841d2a96fbe188cfa96ac
readonly K_RUST_REVISION=c41caa8bede96e279e0b058577dce504e4144f65
readonly PROTECTED_SHA256=dcc35b3bd0c01793c50d3d8096283bd650f591a529d036c79e703ac50fa6d0ec

SCRIPT_DIRECTORY="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
readonly SCRIPT_DIRECTORY
REPOSITORY_ROOT="$(cd -- "$SCRIPT_DIRECTORY/../../.." && pwd -P)"
readonly REPOSITORY_ROOT
KRS_SOURCE="$(cd -- "${KINK_NR07A_KRS_SOURCE:-$REPOSITORY_ROOT/../krs}" && pwd -P)"
readonly KRS_SOURCE
K_RUST_SOURCE="$(cd -- "${KINK_NR07A_K_RUST_SOURCE:-$REPOSITORY_ROOT/../inspirations/midnightntwrk/k-rust-krs-main}" && pwd -P)"
readonly K_RUST_SOURCE
Z3_LIBRARY_DIRECTORY="${KINK_NR07A_Z3_LIB:-}"
if [[ -z "$Z3_LIBRARY_DIRECTORY" ]]; then
    for candidate in /nix/store/*-z3-4.12.5-lib/lib; do
        if [[ -f "$candidate/libz3.so" ]]; then
            Z3_LIBRARY_DIRECTORY="$candidate"
            break
        fi
    done
fi
Z3_LIBRARY_DIRECTORY="$(cd -- "$Z3_LIBRARY_DIRECTORY" && pwd -P)"
readonly Z3_LIBRARY_DIRECTORY
test -f "$Z3_LIBRARY_DIRECTORY/libz3.so"
test "$(z3 --version)" = "Z3 version 4.12.5 - 64 bit"
SCRATCH_PARENT="$(cd -- "${KINK_NR07A_TMPDIR:-/var/tmp}" && pwd -P)"
readonly SCRATCH_PARENT
case "$SCRATCH_PARENT" in
    /*) ;;
    *)
        echo "NR-07A scratch parent is not absolute: $SCRATCH_PARENT" >&2
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
        echo "NR-07A protected artifact SHA-256 is $actual, expected $PROTECTED_SHA256." >&2
        return 1
    fi
    echo "PASS protected artifact SHA-256 $actual"
}

verify_protected_artifact

command -v agent-self >/dev/null
agent-self

if pgrep -x cargo >/dev/null || pgrep -x rustc >/dev/null; then
    echo "NR-07A refuses to overlap another cargo or rustc process." >&2
    ps -eo pid=,comm=,args= | awk '$2 == "cargo" || $2 == "rustc"'
    exit 1
fi

git -c safe.directory="$KRS_SOURCE" -C "$KRS_SOURCE" cat-file -e "$KRS_REVISION^{commit}"
git -c safe.directory="$K_RUST_SOURCE" -C "$K_RUST_SOURCE" cat-file -e "$K_RUST_REVISION^{commit}"

SCRATCH="$(mktemp -d -- "$SCRATCH_PARENT/kink-nr07a.XXXXXX")"
readonly SCRATCH
readonly EXPECTED_PREFIX="$SCRATCH_PARENT/kink-nr07a."
case "$SCRATCH" in
    "$EXPECTED_PREFIX"*) ;;
    *)
        echo "mktemp returned an unexpected NR-07A root: $SCRATCH" >&2
        exit 1
        ;;
esac

cleanup() {
    case "$SCRATCH" in
        "$EXPECTED_PREFIX"*) rm -rf -- "$SCRATCH" ;;
        *) echo "refusing to remove unexpected NR-07A root: $SCRATCH" >&2 ;;
    esac
}
trap cleanup EXIT

readonly CLEAN_ROOT="$SCRATCH/starstream-fv"
readonly CLEAN_KRS="$CLEAN_ROOT/krs"
readonly CLEAN_K_RUST="$CLEAN_ROOT/inspirations/midnightntwrk/k-rust-krs-main"
readonly KRS_TARGET="$SCRATCH/krs-target-z3"
readonly COMPILED_KORE="$SCRATCH/definition.kore"

mkdir -p -- "$(dirname -- "$CLEAN_K_RUST")"
git -c safe.directory="$KRS_SOURCE" clone --shared --no-checkout -- "$KRS_SOURCE" "$CLEAN_KRS"
git -c safe.directory="$CLEAN_KRS" -C "$CLEAN_KRS" checkout --detach "$KRS_REVISION"
git -c safe.directory="$K_RUST_SOURCE" clone --shared --no-checkout -- "$K_RUST_SOURCE" "$CLEAN_K_RUST"
git -c safe.directory="$CLEAN_K_RUST" -C "$CLEAN_K_RUST" checkout --detach "$K_RUST_REVISION"

test -z "$(git -c safe.directory="$CLEAN_KRS" -C "$CLEAN_KRS" status --porcelain)"
test -z "$(git -c safe.directory="$CLEAN_K_RUST" -C "$CLEAN_K_RUST" status --porcelain)"

CARGO_BUILD_JOBS=1 \
CARGO_INCREMENTAL=0 \
CARGO_TARGET_DIR="$KRS_TARGET" \
LIBRARY_PATH="$Z3_LIBRARY_DIRECTORY${LIBRARY_PATH:+:$LIBRARY_PATH}" \
LD_LIBRARY_PATH="$Z3_LIBRARY_DIRECTORY${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}" \
    cargo +stable run \
    --locked \
    --manifest-path "$CLEAN_KRS/Cargo.toml" \
    -p krs-k-rust \
    --bin krs-native-compile \
    -- \
    "$CLEAN_KRS/crates/krs-ir/tests/golden/definition_expr.json" \
    "$COMPILED_KORE"

NR_07A_CLEAN_KRS="$CLEAN_KRS" \
NR_07A_CLEAN_K_RUST="$CLEAN_K_RUST" \
NR_07A_COMPILED_KORE="$COMPILED_KORE" \
CARGO_BUILD_JOBS=1 \
CARGO_INCREMENTAL=0 \
    cargo +stable test \
    --locked \
    --manifest-path "$REPOSITORY_ROOT/Cargo.toml" \
    -p kink-native \
    --test nr_07a_krs_fixture \
    -- \
    --ignored \
    --exact krs_definition_ir_reaches_positive_observed_state_and_path

verify_protected_artifact
