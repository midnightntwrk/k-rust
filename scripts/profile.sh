#!/usr/bin/env bash
set -euo pipefail

# Record a sampling profile of one representative krust workload with samply.
# The workload commands mirror scripts/benchmark.sh so a profile explains the
# numbers that harness reports; the helpers below are copied from it because
# benchmark.sh is not written to be sourced.

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
manifest="$workspace/scripts/reference-differential.toml"

K_CHECKOUT=${K_CHECKOUT:-"$workspace/k"}
IMP_SEMANTICS_CHECKOUT=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
EVM_SEMANTICS_CHECKOUT=${EVM_SEMANTICS_CHECKOUT:-"$workspace/evm-semantics"}
KRUST_BIN=${KRUST_BIN:-"$workspace/target/profiling/krust"}
SAMPLY=${SAMPLY:-samply}
PROFILE_WORK_ROOT=${PROFILE_WORK_ROOT:-"$workspace/target/profiles/work"}

usage() {
  cat <<'EOF'
Usage: scripts/profile.sh --workload imp-compile|imp-prove|kevm-compile [OPTIONS]

Record a sampling profile of one krust workload with samply.

Options:
  --output DIR          Result directory (default: target/profiles/TIMESTAMP-WORKLOAD)
  --claim LABEL         imp-prove only (default: IMP-SIMPLE-SPEC.sum-loop)
  --rate HZ             samply sampling rate (default: 1000)
  --allow-unpinned      Permit checkouts other than the manifest pins
  --allow-sandbox-kevm  Run kevm-compile as an agent-N user (see below)
  --skip-profile        Record everything except the samply profile (see below)
  --dry-run             Print the resolved commands without running them
  -h, --help            Show this help

Requires: samply, jq, and python3 on PATH; KRUST_BIN (default
target/profiling/krust, built with
  cargo build --profile profiling -p k-rust --bin krust --locked);
the same K_CHECKOUT / IMP_SEMANTICS_CHECKOUT / EVM_SEMANTICS_CHECKOUT
variables as scripts/benchmark.sh.

The result directory holds profile.json.gz, command.txt, metadata.json,
the workload's own output, and, when the binary writes them, timings.json
(kprove --timings, kcompile --timings once supported) and counters.json
(KRUST_COUNTERS, a binary built with the measure feature).
Each workload runs twice: once unprofiled through
scripts/conformance/measure.py for the baseline wall time and peak RSS,
then under samply record for the profile.
Open a profile with: samply load DIR/profile.json.gz

--skip-profile leaves out the samply run, for hosts where perf_event_open
is refused (the agent-N sandbox's seccomp filter does that; the script
then fails with samply's message). The unprofiled run, its wall time
and peak RSS, timings.json, and counters.json are still recorded.

kevm-compile is a host-UID workload: it needs gigabytes of memory and a
memory scope (scripts/reference-memory-guard.sh or systemd-run --user
--scope -p MemoryMax=8G). As an agent-N user the script prints the
command and exits 3 unless --allow-sandbox-kevm is given.
EOF
}

fail() {
  echo "error: $*" >&2
  exit 2
}

manifest_value() {
  local section=$1
  local key=$2
  awk -v section="[$section]" -v key="$key" '
    $0 == section { inside = 1; next }
    inside && /^\[/ { exit }
    inside && $1 == key && $2 == "=" {
      value = $0
      sub(/^[^=]*=[[:space:]]*/, "", value)
      gsub(/^"|"$/, "", value)
      print value
      exit
    }
  ' "$manifest"
}

shell_command() {
  local output=
  printf -v output '%q ' "$@"
  printf '%s' "${output% }"
}

check_git_pin() {
  local name=$1
  local checkout=$2
  local expected=$3
  local actual
  [[ -e "$checkout/.git" ]] || fail "$name checkout is missing: $checkout"
  actual=$(git -C "$checkout" rev-parse HEAD)
  if [[ "$actual" != "$expected" && "$allow_unpinned" != 1 ]]; then
    fail "$name checkout is $actual; expected $expected (use --allow-unpinned only for exploratory runs)"
  fi
  if [[ -n "$(git -C "$checkout" status --short --untracked-files=no)" && "$allow_unpinned" != 1 ]]; then
    fail "$name checkout has tracked modifications: $checkout"
  fi
}

builtin_directory="$K_CHECKOUT/k-distribution/include/kframework/builtin"

# Sets the workload's sources and modules; mirrors configure_suite in benchmark.sh.
configure_workload() {
  include_dirs=()
  hook_namespaces=
  markdown_selector=
  plugin_dir=
  case "$1" in
    imp-compile|imp-prove)
      source_checkout=$IMP_SEMANTICS_CHECKOUT
      source_name=IMP
      expected_source_revision=$(manifest_value reference.imp revision)
      compile_source="$source_checkout/src/kimp/kdist/imp-semantics/imp.k"
      compile_main=IMP
      compile_syntax=IMP-SYNTAX
      specification="$source_checkout/examples/specs/imp-simple-spec.k"
      spec_module=IMP-SIMPLE-SPEC
      definition_module=IMP-VERIFICATION
      proof_depth=100
      include_dirs+=("$source_checkout/src/kimp/kdist/imp-semantics")
      work="$PROFILE_WORK_ROOT/imp"
      ;;
    kevm-compile)
      source_checkout=$EVM_SEMANTICS_CHECKOUT
      source_name=KEVM
      expected_source_revision=$(manifest_value reference.kevm revision)
      semantics_dir="$source_checkout/kevm-pyk/src/kevm_pyk/kproj/evm-semantics"
      plugin_dir="$source_checkout/kevm-pyk/src/kevm_pyk/kproj/plugin"
      compile_source="$source_checkout/tests/specs/functional/slot-updates-spec.k"
      compile_main=VERIFICATION
      compile_syntax=VERIFICATION
      include_dirs+=("$semantics_dir" "$plugin_dir")
      hook_namespaces=JSON,KRYPTO
      markdown_selector='k & ! concrete'
      work="$PROFILE_WORK_ROOT/kevm"
      ;;
    *) fail "unknown workload: $1 (expected imp-compile, imp-prove, or kevm-compile)" ;;
  esac
}

append_source_args() {
  local directory
  for directory in "${include_dirs[@]}"; do
    args+=(-I "$directory")
  done
  [[ -z "$hook_namespaces" ]] || args+=(--hook-namespaces "$hook_namespaces")
  [[ -z "$markdown_selector" ]] || args+=(--md-selector "$markdown_selector")
}

# The compile of benchmark.sh's compile phase (run_compile, krust engine).
compile_args() {
  args=(
    "$KRUST_BIN" kcompile "$compile_source"
    --main-module "$compile_main"
    --syntax-module "$compile_syntax"
    --for-proving
    --output-directory "$1"
    --builtin-directory "$builtin_directory"
  )
  append_source_args
  [[ "$kcompile_timings" != 1 ]] || args+=(--timings "$out/timings.json")
}

# The two untimed preparations of benchmark.sh (prepare_krust_proof, run_spec_compile).
prepare_definition_args() {
  args=(
    "$KRUST_BIN" kcompile "$compile_source"
    --main-module "$compile_main"
    --syntax-module "$compile_syntax"
    --for-proving
    --output-directory "$work/krust-definition"
    --builtin-directory "$builtin_directory"
  )
  append_source_args
}

prepare_specification_args() {
  args=(
    "$KRUST_BIN" kcompile "$specification"
    --compiled-definition "$work/krust-definition"
    --main-module "$spec_module"
    --definition-module "$definition_module"
    --for-proving
    --output-directory "$work/krust-specification"
    --builtin-directory "$builtin_directory"
  )
  append_source_args
}

# The proof of benchmark.sh's execute phase (run_execute) with its timings file.
prove_args() {
  args=(
    "$KRUST_BIN" kprove
    --compiled-definition "$work/krust-specification"
    --main-module "$spec_module"
    --claim "$claim"
    --depth "$proof_depth"
    --timings "$out/timings.json"
  )
}

reset_output() {
  local output=$1
  case "$output" in
    "$out"/*|"$PROFILE_WORK_ROOT"/*) ;;
    *) fail "refusing to clean path outside the result or work directory: $output" ;;
  esac
  if [[ -e "$output" ]]; then
    find "$output" -depth -delete
  fi
  mkdir -p "$(dirname "$output")"
}

# Runs a command through measure.py; the log prefix collects stdout, stderr, and meta.toml.
measured() {
  local log=$1
  shift
  python3 "$workspace/scripts/conformance/measure.py" --log "$log" -- "$@"
}

measure_field() {
  sed -n "s/^$2 = //p" "$1.meta.toml"
}

# Runs a command through measured; on failure reports its stderr and stops.
measured_or_fail() {
  local log=$1
  local what=$2
  shift 2
  if ! measured "$log" "$@"; then
    echo "error: $what failed (exit $(measure_field "$log" exit_code)); $log.stderr ends with:" >&2
    tail -n 5 "$log.stderr" >&2
    exit 1
  fi
}

workload=
out=
claim=
rate=1000
allow_unpinned=${PROFILE_ALLOW_UNPINNED:-0}
allow_sandbox_kevm=0
skip_profile=0
dry_run=0

while (($#)); do
  case "$1" in
    --workload) workload=${2:?}; shift 2 ;;
    --output) out=${2:?}; shift 2 ;;
    --claim) claim=${2:?}; shift 2 ;;
    --rate) rate=${2:?}; shift 2 ;;
    --allow-unpinned) allow_unpinned=1; shift ;;
    --allow-sandbox-kevm) allow_sandbox_kevm=1; shift ;;
    --skip-profile) skip_profile=1; shift ;;
    --dry-run) dry_run=1; shift ;;
    -h|--help) usage; exit ;;
    *) fail "unknown option: $1" ;;
  esac
done

[[ -n "$workload" ]] || fail "--workload is required (imp-compile, imp-prove, or kevm-compile)"
configure_workload "$workload"
[[ "$rate" =~ ^[1-9][0-9]*$ ]] || fail "--rate must be a positive integer"
if [[ -n "$claim" && "$workload" != imp-prove ]]; then
  fail "--claim applies to imp-prove only"
fi
[[ "$workload" != imp-prove || -n "$claim" ]] || claim=IMP-SIMPLE-SPEC.sum-loop

if [[ -z "$out" ]]; then
  out="$workspace/target/profiles/$(date -u +%Y%m%dT%H%M%SZ)-$workload"
elif [[ "$out" != /* ]]; then
  out="$workspace/$out"
fi
[[ "$PROFILE_WORK_ROOT" == /* ]] || PROFILE_WORK_ROOT="$workspace/$PROFILE_WORK_ROOT"

kcompile_timings=0
if [[ -x "$KRUST_BIN" ]] && "$KRUST_BIN" kcompile --help 2>/dev/null | grep -q -- --timings; then
  kcompile_timings=1
fi

prepare_commands=()
case "$workload" in
  imp-compile|kevm-compile)
    compile_args "$out/compiled"
    ;;
  imp-prove)
    prepare_definition_args
    prepare_commands+=("$(shell_command "${args[@]}")")
    prepare_specification_args
    prepare_commands+=("$(shell_command "${args[@]}")")
    prove_args
    ;;
esac
workload_args=("${args[@]}")
record_args=(
  "$SAMPLY" record --save-only --rate "$rate" --output "$out/profile.json.gz"
  -- "${workload_args[@]}"
)

if [[ "$dry_run" == 1 ]]; then
  echo "[$workload]"
  for prepare in "${prepare_commands[@]}"; do
    printf 'prepare: %s\n' "$prepare"
  done
  printf 'unprofiled: KRUST_COUNTERS=%q %s\n' "$out/counters.json" "$(shell_command "${workload_args[@]}")"
  [[ "$skip_profile" == 1 ]] || printf 'record: KRUST_COUNTERS=%q %s\n' "$out/counters.json" "$(shell_command "${record_args[@]}")"
  exit
fi

if [[ "$workload" == kevm-compile && "$allow_sandbox_kevm" != 1 && "$(id -un)" =~ ^agent-[0-9]+$ ]]; then
  {
    echo "kevm-compile is a host-UID workload; as $(id -un) it needs --allow-sandbox-kevm and a memory scope."
    echo "The command it would record is:"
    printf '  KRUST_COUNTERS=%q %s\n' "$out/counters.json" "$(shell_command "${record_args[@]}")"
  } >&2
  exit 3
fi

[[ "$skip_profile" == 1 ]] || command -v "$SAMPLY" >/dev/null 2>&1 || fail "samply is required (SAMPLY=$SAMPLY)"
command -v jq >/dev/null 2>&1 || fail "jq is required to check the profile and record metadata"
command -v python3 >/dev/null 2>&1 || fail "python3 is required for scripts/conformance/measure.py"
[[ -x "$KRUST_BIN" ]] || fail "krust binary is missing: $KRUST_BIN (run cargo build --profile profiling -p k-rust --bin krust --locked)"
if command -v readelf >/dev/null 2>&1; then
  readelf -S "$KRUST_BIN" | grep -q '\.debug_line' || fail "KRUST_BIN has no line tables; build with --profile profiling"
else
  echo "note: readelf is not on PATH; not checking that $KRUST_BIN has line tables" >&2
fi
check_git_pin K "$K_CHECKOUT" "$(manifest_value reference.k revision)"
check_git_pin "$source_name" "$source_checkout" "$expected_source_revision"
if [[ "$workload" == kevm-compile ]]; then
  check_git_pin KEVM-plugin "$plugin_dir" "$(manifest_value reference.kevm-plugin revision)"
fi
[[ -f "$compile_source" ]] || fail "missing definition: $compile_source"
[[ "$workload" != imp-prove || -f "$specification" ]] || fail "missing specification: $specification"
for directory in "${include_dirs[@]}"; do
  [[ -d "$directory" ]] || fail "missing include directory: $directory"
done

mkdir -p "$out"
if [[ "$workload" == imp-prove ]]; then
  # Prepared artifacts are reused across runs like benchmark.sh's work root;
  # use a fresh PROFILE_WORK_ROOT after a compiler or option change.
  mkdir -p "$work"
  if [[ ! -f "$work/krust-definition/krust.json" || ! -f "$work/krust-definition/parsed.json" ]]; then
    echo "[$workload] preparing proof-ready krust definition"
    prepare_definition_args
    "${args[@]}"
  fi
  if [[ ! -f "$work/krust-specification/krust.json" ]]; then
    echo "[$workload] compiling the specification against prepared semantics"
    prepare_specification_args
    "${args[@]}"
  fi
fi

{
  for prepare in "${prepare_commands[@]}"; do
    printf 'prepare: %s\n' "$prepare"
  done
  printf 'unprofiled: KRUST_COUNTERS=%q %s\n' "$out/counters.json" "$(shell_command "${workload_args[@]}")"
  [[ "$skip_profile" == 1 ]] || printf 'record: KRUST_COUNTERS=%q %s\n' "$out/counters.json" "$(shell_command "${record_args[@]}")"
} >"$out/command.txt"

export KRUST_COUNTERS="$out/counters.json"
echo "[$workload] unprofiled run for wall time and peak RSS"
measured_or_fail "$out/unprofiled" "the unprofiled $workload run" "${workload_args[@]}"

sample_count=null
profiled_wall=null
profiled_rss=null
profiled_exit=null
if [[ "$skip_profile" != 1 ]]; then
  [[ "$workload" == imp-prove ]] || reset_output "$out/compiled"
  echo "[$workload] recording at $rate Hz"
  measured_or_fail "$out/profiled" "samply record" "${record_args[@]}"
  sample_count=$(gunzip -c "$out/profile.json.gz" | jq '[.threads[].samples.length] | add // 0')
  if [[ "$sample_count" == 0 ]]; then
    fail "profile has 0 samples: $out/profile.json.gz (perf_event delivered nothing; see benchmarks/README.md, Profiling)"
  fi
  profiled_wall=$(measure_field "$out/profiled" wall_seconds)
  profiled_rss=$(measure_field "$out/profiled" peak_rss_kib)
  profiled_exit=$(measure_field "$out/profiled" exit_code)
fi

cpu=unknown
memory=unknown
if [[ -r /proc/cpuinfo ]]; then
  cpu=$(awk -F: '/model name/ { sub(/^[[:space:]]*/, "", $2); print $2; exit }' /proc/cpuinfo)
  memory=$(awk '/MemTotal/ { print $2 * 1024; exit }' /proc/meminfo)
fi
plugin_revision=
[[ -z "$plugin_dir" ]] || plugin_revision=$(git -C "$plugin_dir" rev-parse HEAD)
jq -n \
  --arg workload "$workload" \
  --arg claim "$claim" \
  --arg timestamp "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
  --arg system "$(uname -a)" \
  --arg kernel "$(uname -r)" \
  --arg cpu "$cpu" \
  --arg memory_bytes "$memory" \
  --arg user "$(id -un)" \
  --arg rust_revision "$(git -C "$workspace" rev-parse HEAD)" \
  --argjson rust_dirty "$([[ -n "$(git -C "$workspace" status --porcelain --untracked-files=no)" ]] && echo true || echo false)" \
  --arg k_revision "$(git -C "$K_CHECKOUT" rev-parse HEAD)" \
  --arg semantics_revision "$(git -C "$source_checkout" rev-parse HEAD)" \
  --arg plugin_revision "$plugin_revision" \
  --arg krust_version "$("$KRUST_BIN" --version)" \
  --arg krust_path "$KRUST_BIN" \
  --arg krust_sha256 "$(sha256sum "$KRUST_BIN" | cut -d' ' -f1)" \
  --arg rustc_version "$(rustc --version 2>/dev/null || echo unavailable)" \
  --arg samply_version "$("$SAMPLY" --version)" \
  --argjson rate "$rate" \
  --argjson sample_count "$sample_count" \
  --argjson unprofiled_wall "$(measure_field "$out/unprofiled" wall_seconds)" \
  --argjson unprofiled_rss "$(measure_field "$out/unprofiled" peak_rss_kib)" \
  --argjson unprofiled_exit "$(measure_field "$out/unprofiled" exit_code)" \
  --argjson profiled_wall "$profiled_wall" \
  --argjson profiled_rss "$profiled_rss" \
  --argjson profiled_exit "$profiled_exit" \
  --argjson counters "$([[ -f "$out/counters.json" ]] && echo true || echo false)" \
  --argjson timings "$([[ -f "$out/timings.json" ]] && echo true || echo false)" \
  '{
    workload: $workload,
    claim: (if $claim == "" then null else $claim end),
    timestamp: $timestamp,
    user: $user,
    host: {system: $system, kernel: $kernel, cpu: $cpu, memory_bytes: $memory_bytes},
    revisions: {
      krust: $rust_revision, krust_dirty: $rust_dirty, k: $k_revision,
      semantics: $semantics_revision,
      plugin: (if $plugin_revision == "" then null else $plugin_revision end)
    },
    tools: {krust: $krust_version, rustc: $rustc_version, samply: $samply_version},
    binary: {path: $krust_path, sha256: $krust_sha256},
    sampling: {rate_hz: $rate, sample_count: $sample_count},
    unprofiled: {wall_seconds: $unprofiled_wall, peak_rss_kib: $unprofiled_rss, exit_code: $unprofiled_exit},
    profiled: (if $profiled_exit == null then null else
      {wall_seconds: $profiled_wall, peak_rss_kib: $profiled_rss, exit_code: $profiled_exit,
       note: "measured around samply record; wall includes profile serialisation and peak RSS is the larger of samply and krust"} end),
    outputs: {counters_json: $counters, timings_json: $timings}
  }' >"$out/metadata.json"

if [[ "$skip_profile" == 1 ]]; then
  echo "[$workload] no profile recorded (--skip-profile); results in $out"
else
  echo "[$workload] $sample_count samples; results in $out"
  echo "next: $SAMPLY load $(shell_command "$out/profile.json.gz")"
fi
