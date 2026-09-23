#!/usr/bin/env bash
set -euo pipefail

# Record which functions of the workspace one receipt workload executed, as the
# coverage.toml that `algo-graph join --coverage` reads.

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

usage() {
  cat <<'EOF'
Usage: scripts/coverage-receipt.sh --workload imp-prove|light-gate-append --krust BIN --output DIR [OPTIONS]

Run one receipt workload with a coverage-instrumented krust and write
DIR/coverage.toml (the executed and unexecuted workspace functions) and
DIR/coverage-command.txt (every command this script ran).

The coverage run is a separate execution of the receipt's measured command,
with the same arguments, the same inputs and the same --timings, --trace and
KRUST_COUNTERS outputs (written below the work directory).
Its function counts apply to the receipt because krust is deterministic on
these inputs: the instrumented run and the receipt's run execute the same
code. Compare the counters.json of both runs to check that for one receipt.
Every instrumented invocation sets LLVM_PROFILE_FILE; the merged profile holds
only the measured command's profile, never the prepare steps'.

Options:
  --workload NAME     imp-prove or light-gate-append
  --krust BIN         krust built with -C instrument-coverage and the measure
                      feature, from the checkout named by --source-root:
                        RUSTFLAGS="-C instrument-coverage" \
                        LLVM_PROFILE_FILE="$CARGO_TARGET_DIR/build-profiles/%p-%m.profraw" \
                        cargo build -p k-rust --bin krust --features measure
                      Instrumented build scripts and procedural macros write a
                      profile when they run; without LLVM_PROFILE_FILE they
                      write default_*.profraw into the checkout and the
                      Cargo registry sources.
  --output DIR        Directory that receives coverage.toml and
                      coverage-command.txt
  --work DIR          Work directory for prepared definitions, run outputs,
                      raw profiles and the llvm-cov export
                      (default: target/coverage/WORKLOAD)
  --prepare-krust BIN krust used for the prepare steps (default: --krust;
                      no profile is collected from the prepare steps)
  --source-root DIR   Checkout that built --krust; coverage.toml names files
                      relative to it and records their digests
                      (default: this script's checkout)
  --algo-graph BIN    algo-graph binary (default: cargo run -p algo-graph)
  -h, --help          Show this help

Environment: K_CHECKOUT and IMP_SEMANTICS_CHECKOUT (default: SOURCE_ROOT/k and
SOURCE_ROOT/imp-semantics), LLVM_TOOLS (directory holding llvm-profdata and
llvm-cov; default: the llvm-tools component of the active Rust toolchain).
EOF
}

fail() {
  echo "error: $*" >&2
  exit 2
}

workload=""
krust=""
output=""
work=""
prepare_krust=""
source_root="$workspace"
algo_graph=""
while (($#)); do
  case "$1" in
    --workload) workload=${2:?}; shift 2 ;;
    --krust) krust=${2:?}; shift 2 ;;
    --output) output=${2:?}; shift 2 ;;
    --work) work=${2:?}; shift 2 ;;
    --prepare-krust) prepare_krust=${2:?}; shift 2 ;;
    --source-root) source_root=${2:?}; shift 2 ;;
    --algo-graph) algo_graph=${2:?}; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) fail "unknown argument: $1" ;;
  esac
done

[[ -n "$workload" ]] || fail "--workload is required"
[[ -x "$krust" ]] || fail "--krust must name an executable"
[[ -n "$output" ]] || fail "--output is required"
source_root=$(cd "$source_root" && pwd)
prepare_krust=${prepare_krust:-$krust}
work=${work:-"$source_root/target/coverage/$workload"}
K_CHECKOUT=${K_CHECKOUT:-"$source_root/k"}
IMP_SEMANTICS_CHECKOUT=${IMP_SEMANTICS_CHECKOUT:-"$source_root/imp-semantics"}
LLVM_TOOLS=${LLVM_TOOLS:-"$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | sed -n 's/^host: //p')/bin"}
[[ -x "$LLVM_TOOLS/llvm-profdata" && -x "$LLVM_TOOLS/llvm-cov" ]] \
  || fail "llvm-profdata and llvm-cov are missing from $LLVM_TOOLS (rustup component add llvm-tools)"
if [[ -n "$algo_graph" ]]; then
  algo_graph_command=("$algo_graph")
else
  algo_graph_command=(cargo run --quiet --manifest-path "$workspace/Cargo.toml" -p algo-graph --)
fi

builtin="$K_CHECKOUT/k-distribution/include/kframework/builtin"
imp="$IMP_SEMANTICS_CHECKOUT/src/kimp/kdist/imp-semantics"
run="$work/run"
profiles="$work/profiles"
rm -rf "$run" "$profiles" "$work/prepare-profiles"
mkdir -p "$run" "$profiles" "$work/prepare-profiles" "$output"
log="$output/coverage-command.txt"
: >"$log"

# Print one command to the log with a label, then run it.
record() {
  local label=$1
  shift
  printf '%s: %s\n' "$label" "$*" >>"$log"
  "$@"
}

prepare() {
  record prepare env LLVM_PROFILE_FILE="$work/prepare-profiles/%p.profraw" "$prepare_krust" "$@" >/dev/null
}

case "$workload" in
  imp-prove)
    definition="$work/krust-definition"
    specification="$work/krust-specification"
    rm -rf "$definition" "$specification"
    prepare kcompile "$imp/imp.k" --main-module IMP --syntax-module IMP-SYNTAX --for-proving \
      --output-directory "$definition" --builtin-directory "$builtin" -I "$imp"
    prepare kcompile "$IMP_SEMANTICS_CHECKOUT/examples/specs/imp-simple-spec.k" \
      --compiled-definition "$definition" --main-module IMP-SIMPLE-SPEC \
      --definition-module IMP-VERIFICATION --for-proving --output-directory "$specification" \
      --builtin-directory "$builtin" -I "$imp"
    measured=("$krust" kprove --compiled-definition "$specification" --main-module IMP-SIMPLE-SPEC
      --claim IMP-SIMPLE-SPEC.sum-loop --depth 100 --timings "$run/timings.json"
      --trace "$run/trace.json")
    ;;
  light-gate-append)
    rm -rf "$run/kompiled"
    measured=("$krust" kcompile "$K_CHECKOUT/k-distribution/tests/regression-new/append/test.k"
      --main-module TEST --output-directory "$run/kompiled" --builtin-directory "$builtin"
      --timings "$run/timings.json" --trace "$run/trace.json")
    ;;
  *) fail "unknown workload: $workload (expected imp-prove or light-gate-append)" ;;
esac
rm -rf "$work/prepare-profiles"

record measured env LLVM_PROFILE_FILE="$profiles/%p-%m.profraw" KRUST_COUNTERS="$run/counters.json" \
  "${measured[@]}" >"$run/stdout" 2>"$run/stderr"
record merge "$LLVM_TOOLS/llvm-profdata" merge --sparse "$profiles"/*.profraw -o "$work/coverage.profdata"
printf 'export: %s\n' "$LLVM_TOOLS/llvm-cov export --format=text --instr-profile $work/coverage.profdata --ignore-filename-regex=^[^/]|/\\.cargo/|/rustc/ $krust > $work/export.json" >>"$log"
"$LLVM_TOOLS/llvm-cov" export --format=text --instr-profile "$work/coverage.profdata" \
  '--ignore-filename-regex=^[^/]|/\.cargo/|/rustc/' "$krust" >"$work/export.json"
record normalize "${algo_graph_command[@]}" coverage --export "$work/export.json" \
  --source-root "$source_root" --binary "$krust" -o "$output/coverage.toml"
