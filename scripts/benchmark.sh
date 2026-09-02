#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
script="$workspace/scripts/benchmark.sh"
manifest="$workspace/scripts/reference-differential.toml"

K_CHECKOUT=${K_CHECKOUT:-"$workspace/k"}
IMP_SEMANTICS_CHECKOUT=${IMP_SEMANTICS_CHECKOUT:-"$workspace/imp-semantics"}
EVM_SEMANTICS_CHECKOUT=${EVM_SEMANTICS_CHECKOUT:-"$workspace/evm-semantics"}
KRUST_BIN=${KRUST_BIN:-"$workspace/target/release/krust"}
K_KOMPILE=${K_KOMPILE:-}
K_KPROVE=${K_KPROVE:-}
HYPERFINE=${HYPERFINE:-hyperfine}
REFERENCE_K_OPTS=${REFERENCE_K_OPTS:-'-Xmx4096m -Xss4m -Dscala.concurrent.context.numThreads=1 -Dscala.concurrent.context.maxThreads=1'}
GHCRTS=${GHCRTS-}

usage() {
  cat <<'EOF'
Usage: scripts/benchmark.sh [OPTIONS]

Compare release-mode krust with canonical K's Haskell backend.

Options:
  --suite imp|kevm|all       Benchmark suite (default: all)
  --phase compile|prove|all  Benchmark phase (default: all)
  --claim LABEL             Benchmark one claim (requires one suite and a proof phase)
  --runs N                   Override the suite/phase run count
  --warmup N                 Override the suite/phase warmup count
  --output DIR               Result directory (default: target/benchmarks/results/TIMESTAMP)
  --skip-preflight           Skip untimed correctness runs
  --allow-unpinned           Permit source/tool revisions other than the manifest pins
  --dry-run                  Print the resolved benchmark commands without running them
  --list                     List benchmark cases
  -h, --help                 Show this help

Required tools: hyperfine, a release krust binary, and matching canonical
kompile/kprove executables selected with K_KOMPILE and K_KPROVE.
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

configure_suite() {
  benchmark_suite=$1
  include_dirs=()
  hook_namespaces=
  markdown_selector=
  case "$benchmark_suite" in
    imp)
      source_checkout=$IMP_SEMANTICS_CHECKOUT
      expected_source_revision=$(manifest_value reference.imp revision)
      source_name=IMP
      compile_source="$source_checkout/src/kimp/kdist/imp-semantics/imp.k"
      compile_main=IMP
      compile_syntax=IMP-SYNTAX
      specification="$source_checkout/examples/specs/imp-simple-spec.k"
      spec_module=IMP-SIMPLE-SPEC
      definition_module=IMP-VERIFICATION
      proof_depth=100
      proof_claims=(
        IMP-SIMPLE-SPEC.addition-var
        IMP-SIMPLE-SPEC.branching-program
        IMP-SIMPLE-SPEC.sum-loop
      )
      include_dirs+=("$source_checkout/src/kimp/kdist/imp-semantics")
      ;;
    kevm)
      source_checkout=$EVM_SEMANTICS_CHECKOUT
      expected_source_revision=$(manifest_value reference.kevm revision)
      source_name=KEVM
      semantics_dir="$source_checkout/kevm-pyk/src/kevm_pyk/kproj/evm-semantics"
      plugin_dir="$source_checkout/kevm-pyk/src/kevm_pyk/kproj/plugin"
      compile_source="$source_checkout/tests/specs/functional/slot-updates-spec.k"
      compile_main=VERIFICATION
      compile_syntax=VERIFICATION
      specification=$compile_source
      spec_module=SLOT-UPDATES-SPEC
      definition_module=VERIFICATION
      proof_depth=100
      proof_claims=(SLOT-UPDATES-SPEC.gfob-min)
      include_dirs+=("$semantics_dir" "$plugin_dir")
      hook_namespaces=JSON,KRYPTO
      markdown_selector='k & ! concrete'
      ;;
    *) fail "unknown benchmark suite: $benchmark_suite" ;;
  esac
}

append_source_args() {
  local target=$1
  local directory
  for directory in "${include_dirs[@]}"; do
    if [[ "$target" == reference ]]; then
      reference_args+=(-I "$directory")
    else
      rust_args+=(-I "$directory")
    fi
  done
}

reset_output() {
  local output=$1
  case "$output" in
    "$BENCHMARK_WORK_ROOT"/*) ;;
    *) fail "refusing to clean path outside benchmark work root: $output" ;;
  esac
  if [[ -e "$output" ]]; then
    find "$output" -depth -delete
  fi
  mkdir -p "$(dirname "$output")"
}

run_compile() {
  local engine=$1
  local work=$2
  local output="$work/compile-$engine"
  if [[ "$engine" == canonical-haskell ]]; then
    reference_args=(
      "$K_KOMPILE" "$compile_source"
      --backend haskell
      --main-module "$compile_main"
      --syntax-module "$compile_syntax"
      --output-definition "$output"
      --warnings none
    )
    append_source_args reference
    [[ -z "$hook_namespaces" ]] || reference_args+=(--hook-namespaces "$hook_namespaces")
    [[ -z "$markdown_selector" ]] || reference_args+=(--md-selector "$markdown_selector")
    K_OPTS=$REFERENCE_K_OPTS GHCRTS=$GHCRTS "${reference_args[@]}"
  elif [[ "$engine" == krust ]]; then
    rust_args=(
      "$KRUST_BIN" kcompile "$compile_source"
      --main-module "$compile_main"
      --syntax-module "$compile_syntax"
      --output-directory "$output"
      --builtin-directory "$K_CHECKOUT/k-distribution/include/kframework/builtin"
    )
    append_source_args rust
    [[ -z "$hook_namespaces" ]] || rust_args+=(--hook-namespaces "$hook_namespaces")
    [[ -z "$markdown_selector" ]] || rust_args+=(--md-selector "$markdown_selector")
    "${rust_args[@]}"
  else
    fail "unknown benchmark engine: $engine"
  fi
}

prepare_compile() {
  local engine=$1
  local work=$2
  reset_output "$work/compile-$engine"
}

prepare_proof() {
  local work=$1
  local output="$work/reference-definition"
  reset_output "$output"
  reference_args=(
    "$K_KOMPILE" "$compile_source"
    --backend haskell
    --main-module "$compile_main"
    --syntax-module "$compile_syntax"
    --output-definition "$output"
    --warnings none
  )
  append_source_args reference
  [[ -z "$hook_namespaces" ]] || reference_args+=(--hook-namespaces "$hook_namespaces")
  [[ -z "$markdown_selector" ]] || reference_args+=(--md-selector "$markdown_selector")
  K_OPTS=$REFERENCE_K_OPTS GHCRTS=$GHCRTS "${reference_args[@]}"
}

run_proof() {
  local engine=$1
  local claim=$2
  local work=$3
  if [[ "$engine" == canonical-haskell ]]; then
    reference_args=(
      "$K_KPROVE" "$specification"
      --definition "$work/reference-definition"
      --spec-module "$spec_module"
      --claims "$claim"
      --depth "$proof_depth"
      --output none
      --warnings none
    )
    append_source_args reference
    K_OPTS=$REFERENCE_K_OPTS GHCRTS=$GHCRTS "${reference_args[@]}"
  elif [[ "$engine" == krust ]]; then
    rust_args=(
      "$KRUST_BIN" kprove "$specification"
      --main-module "$spec_module"
      --definition-module "$definition_module"
      --claim "$claim"
      --depth "$proof_depth"
      --builtin-directory "$K_CHECKOUT/k-distribution/include/kframework/builtin"
    )
    append_source_args rust
    "${rust_args[@]}"
  else
    fail "unknown benchmark engine: $engine"
  fi
}

shell_command() {
  local output=
  printf -v output '%q ' "$@"
  printf '%s' "${output% }"
}

command_for() {
  local phase=$1
  local engine=$2
  local suite=$3
  local work=$4
  local claim=${5:-}
  if [[ "$phase" == compile ]]; then
    shell_command "$script" __run compile "$engine" "$suite" "$work"
  else
    shell_command "$script" __run prove "$engine" "$suite" "$work" "$claim"
  fi
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

check_tools_and_sources() {
  local expected_k_revision
  local expected_k_version
  local actual_k_version
  command -v "$HYPERFINE" >/dev/null 2>&1 || fail "hyperfine is required"
  [[ -x "$KRUST_BIN" ]] || fail "release krust binary is missing: $KRUST_BIN (run cargo build --release -p k-rust --bin krust)"
  expected_k_revision=$(manifest_value reference.k revision)
  check_git_pin K "$K_CHECKOUT" "$expected_k_revision"
  configure_suite "$1"
  if [[ -z "$K_KOMPILE" ]]; then
    K_KOMPILE=$(command -v kompile || true)
  fi
  [[ -n "$K_KOMPILE" && -x "$K_KOMPILE" ]] || fail "set K_KOMPILE to canonical K's kompile executable"
  if [[ -z "$K_KPROVE" ]]; then
    K_KPROVE="$(dirname "$K_KOMPILE")/kprove"
  fi
  [[ -x "$K_KPROVE" ]] || fail "set K_KPROVE to the matching canonical kprove executable"
  expected_k_version=$(manifest_value reference.k version)
  actual_k_version=$($K_KOMPILE --version | sed -n 's/^K version:[[:space:]]*//p')
  if [[ "$actual_k_version" != "$expected_k_version" && "$allow_unpinned" != 1 ]]; then
    fail "canonical K is ${actual_k_version:-unknown}; expected $expected_k_version"
  fi
  check_git_pin "$source_name" "$source_checkout" "$expected_source_revision"
  if [[ "$1" == kevm ]]; then
    check_git_pin KEVM-plugin "$plugin_dir" "$(manifest_value reference.kevm-plugin revision)"
  fi
  [[ -f "$compile_source" ]] || fail "missing benchmark definition: $compile_source"
  [[ -f "$specification" ]] || fail "missing benchmark specification: $specification"
  local directory
  for directory in "${include_dirs[@]}"; do
    [[ -d "$directory" ]] || fail "missing include directory: $directory"
  done
}

write_metadata() {
  local suite=$1
  local phase=$2
  local result_dir=$3
  local cpu=unknown
  local memory=unknown
  local canonical_version
  canonical_version=$($K_KOMPILE --version | tr '\n' ' ')
  if command -v sysctl >/dev/null 2>&1; then
    cpu=$(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown)
    memory=$(sysctl -n hw.memsize 2>/dev/null || echo unknown)
  elif [[ -r /proc/cpuinfo ]]; then
    cpu=$(awk -F: '/model name/ { sub(/^[[:space:]]*/, "", $2); print $2; exit }' /proc/cpuinfo)
    memory=$(awk '/MemTotal/ { print $2 * 1024; exit }' /proc/meminfo)
  fi
  jq -n \
    --arg suite "$suite" \
    --arg phase "$phase" \
    --arg timestamp "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg system "$(uname -a)" \
    --arg cpu "$cpu" \
    --arg memory_bytes "$memory" \
    --arg rust_revision "$(git -C "$workspace" rev-parse HEAD)" \
    --arg k_revision "$(git -C "$K_CHECKOUT" rev-parse HEAD)" \
    --arg semantics_revision "$(git -C "$source_checkout" rev-parse HEAD)" \
    --arg krust_version "$($KRUST_BIN --version)" \
    --arg rustc_version "$(rustc --version 2>/dev/null || echo unavailable)" \
    --arg canonical_version "$canonical_version" \
    --arg hyperfine_version "$($HYPERFINE --version)" \
    --arg ghcrts "$GHCRTS" \
    --arg k_opts "$REFERENCE_K_OPTS" \
    '{
      suite: $suite,
      phase: $phase,
      timestamp: $timestamp,
      host: {system: $system, cpu: $cpu, memory_bytes: $memory_bytes},
      revisions: {krust: $rust_revision, k: $k_revision, semantics: $semantics_revision},
      tools: {krust: $krust_version, rustc: $rustc_version, canonical: $canonical_version, hyperfine: $hyperfine_version},
      environment: {GHCRTS: $ghcrts, K_OPTS: $k_opts}
    }' >"$result_dir/metadata.json"
}

append_summary() {
  local suite=$1
  local case_name=$2
  local result_json=$3
  local row
  row=$(jq -r --arg suite "$suite" --arg case_name "$case_name" '
    def result($name): .results[] | select(.command == $name);
    (result("canonical-haskell")) as $canonical
    | (result("krust")) as $rust
    | [
        $suite,
        $case_name,
        ($canonical.mean | tostring),
        ($rust.mean | tostring),
        ($rust.mean / $canonical.mean | tostring)
      ]
    | @tsv
  ' "$result_json")
  IFS=$'\t' read -r row_suite row_case canonical_mean rust_mean relative <<<"$row"
  printf '| %s | %s | %.3f | %.3f | %.2fx |\n' \
    "$row_suite" "$row_case" "$canonical_mean" "$rust_mean" "$relative" \
    >>"$results_root/summary.md"
}

default_runs() {
  case "$1:$2" in
    compile:imp) echo 3 ;;
    compile:kevm) echo 1 ;;
    prove:imp) echo 5 ;;
    prove:kevm) echo 1 ;;
  esac
}

default_warmup() {
  if [[ "$1:$2" == prove:imp ]]; then echo 1; else echo 0; fi
}

benchmark_pair() {
  local suite=$1
  local phase=$2
  local claim=${3:-}
  local case_name=$phase
  [[ -z "$claim" ]] || case_name="prove-${claim##*.}"
  local result_dir="$results_root/$suite/$case_name"
  local work="$BENCHMARK_WORK_ROOT/$suite"
  local selected_runs=${runs_override:-$(default_runs "$phase" "$suite")}
  local selected_warmup=${warmup_override:-$(default_warmup "$phase" "$suite")}
  local canonical_command
  local rust_command
  local canonical_prepare=
  local rust_prepare=
  canonical_command=$(command_for "$phase" canonical-haskell "$suite" "$work" "$claim")
  rust_command=$(command_for "$phase" krust "$suite" "$work" "$claim")
  if [[ "$phase" == compile ]]; then
    canonical_prepare=$(shell_command "$script" __prepare-compile canonical-haskell "$suite" "$work")
    rust_prepare=$(shell_command "$script" __prepare-compile krust "$suite" "$work")
  fi
  mkdir -p "$result_dir" "$work"
  {
    [[ -z "$canonical_prepare" ]] || printf 'canonical-haskell prepare: %s\n' "$canonical_prepare"
    printf 'canonical-haskell: %s\n' "$canonical_command"
    [[ -z "$rust_prepare" ]] || printf 'krust prepare: %s\n' "$rust_prepare"
    printf 'krust: %s\n' "$rust_command"
  } >"$result_dir/commands.txt"
  if [[ "$dry_run" == 1 ]]; then
    echo "[$suite:$case_name]"
    cat "$result_dir/commands.txt"
    return
  fi
  if [[ "$phase" == prove && ! -d "$work/reference-definition" ]]; then
    echo "[$suite] preparing canonical Haskell definition"
    "$script" __prepare-proof "$suite" "$work"
  fi
  if [[ "$skip_preflight" != 1 ]]; then
    echo "[$suite:$case_name] correctness preflight"
    "$script" __check "$phase" canonical-haskell "$suite" "$work" "$claim" >"$result_dir/canonical-preflight.log" 2>&1
    "$script" __check "$phase" krust "$suite" "$work" "$claim" >"$result_dir/krust-preflight.log" 2>&1
  fi
  write_metadata "$suite" "$case_name" "$result_dir"
  echo "[$suite:$case_name] benchmarking $selected_runs run(s), $selected_warmup warmup(s)"
  hyperfine_args=(
    --style basic \
    --sort command \
    --runs "$selected_runs" \
    --warmup "$selected_warmup" \
  )
  [[ -z "$canonical_prepare" ]] || hyperfine_args+=(--prepare "$canonical_prepare")
  [[ -z "$rust_prepare" ]] || hyperfine_args+=(--prepare "$rust_prepare")
  "$HYPERFINE" "${hyperfine_args[@]}" \
    --command-name canonical-haskell "$canonical_command" \
    --command-name krust "$rust_command" \
    --export-json "$result_dir/results.json" \
    --export-markdown "$result_dir/results.md"
  append_summary "$suite" "$case_name" "$result_dir/results.json"
}

if [[ "${1:-}" == __run ]]; then
  shift
  internal_phase=$1
  internal_engine=$2
  internal_suite=$3
  internal_work=$4
  internal_claim=${5:-}
  BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:?}
  configure_suite "$internal_suite"
  if [[ "$internal_phase" == compile ]]; then
    run_compile "$internal_engine" "$internal_work"
  else
    run_proof "$internal_engine" "$internal_claim" "$internal_work"
  fi
  exit
fi

if [[ "${1:-}" == __prepare-proof ]]; then
  shift
  BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:?}
  configure_suite "$1"
  prepare_proof "$2"
  exit
fi

if [[ "${1:-}" == __prepare-compile ]]; then
  shift
  BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:?}
  internal_engine=$1
  internal_suite=$2
  internal_work=$3
  configure_suite "$internal_suite"
  prepare_compile "$internal_engine" "$internal_work"
  exit
fi

if [[ "${1:-}" == __check ]]; then
  shift
  internal_phase=$1
  internal_engine=$2
  internal_suite=$3
  internal_work=$4
  internal_claim=${5:-}
  BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:?}
  configure_suite "$internal_suite"
  if [[ "$internal_phase" == compile ]]; then
    prepare_compile "$internal_engine" "$internal_work"
    run_compile "$internal_engine" "$internal_work"
  elif [[ "$internal_engine" == krust ]]; then
    proof_status=0
    proof_output=$(run_proof "$internal_engine" "$internal_claim" "$internal_work" 2>&1) || proof_status=$?
    printf '%s\n' "$proof_output"
    [[ "$proof_status" == 0 ]] || exit "$proof_status"
    grep -Fq "claim $internal_claim: proven" <<<"$proof_output" || fail "krust did not prove $internal_claim"
  else
    run_proof "$internal_engine" "$internal_claim" "$internal_work"
  fi
  exit
fi

suite=all
phase=all
claim_override=
runs_override=
warmup_override=
results_root=
skip_preflight=0
allow_unpinned=${BENCHMARK_ALLOW_UNPINNED:-0}
dry_run=0
list_only=0

while (($#)); do
  case "$1" in
    --suite) suite=${2:?}; shift 2 ;;
    --phase) phase=${2:?}; shift 2 ;;
    --claim) claim_override=${2:?}; shift 2 ;;
    --runs) runs_override=${2:?}; shift 2 ;;
    --warmup) warmup_override=${2:?}; shift 2 ;;
    --output) results_root=${2:?}; shift 2 ;;
    --skip-preflight) skip_preflight=1; shift ;;
    --allow-unpinned) allow_unpinned=1; shift ;;
    --dry-run) dry_run=1; shift ;;
    --list) list_only=1; shift ;;
    -h|--help) usage; exit ;;
    *) fail "unknown option: $1" ;;
  esac
done

case "$suite" in imp|kevm|all) ;; *) fail "--suite must be imp, kevm, or all" ;; esac
case "$phase" in compile|prove|all) ;; *) fail "--phase must be compile, prove, or all" ;; esac
[[ -z "$runs_override" || "$runs_override" =~ ^[1-9][0-9]*$ ]] || fail "--runs must be positive"
[[ -z "$warmup_override" || "$warmup_override" =~ ^[0-9]+$ ]] || fail "--warmup must be non-negative"
if [[ -n "$claim_override" ]]; then
  [[ "$suite" != all ]] || fail "--claim requires --suite imp or --suite kevm"
  [[ "$phase" != compile ]] || fail "--claim cannot be used with --phase compile"
  configure_suite "$suite"
  claim_found=0
  for known_claim in "${proof_claims[@]}"; do
    if [[ "$known_claim" == "$claim_override" ]]; then
      claim_found=1
      break
    fi
  done
  [[ "$claim_found" == 1 ]] || fail "unknown $suite claim: $claim_override (use --list)"
fi

if [[ "$list_only" == 1 ]]; then
  cat <<'EOF'
imp/compile
imp/prove/IMP-SIMPLE-SPEC.addition-var
imp/prove/IMP-SIMPLE-SPEC.branching-program
imp/prove/IMP-SIMPLE-SPEC.sum-loop
kevm/compile
kevm/prove/SLOT-UPDATES-SPEC.gfob-min
EOF
  exit
fi

if [[ -z "$results_root" ]]; then
  results_root="$workspace/target/benchmarks/results/$(date -u +%Y%m%dT%H%M%SZ)"
elif [[ "$results_root" != /* ]]; then
  results_root="$workspace/$results_root"
fi
BENCHMARK_WORK_ROOT="$workspace/target/benchmarks/work"
export K_CHECKOUT IMP_SEMANTICS_CHECKOUT EVM_SEMANTICS_CHECKOUT KRUST_BIN K_KOMPILE K_KPROVE
export HYPERFINE REFERENCE_K_OPTS GHCRTS BENCHMARK_WORK_ROOT

suites=()
phases=()
if [[ "$suite" == all ]]; then suites=(imp kevm); else suites=("$suite"); fi
if [[ "$phase" == all ]]; then phases=(compile prove); else phases=("$phase"); fi

if [[ "$dry_run" != 1 ]]; then
  command -v jq >/dev/null 2>&1 || fail "jq is required to record benchmark metadata"
  for selected_suite in "${suites[@]}"; do
    check_tools_and_sources "$selected_suite"
  done
fi

mkdir -p "$results_root"
if [[ "$dry_run" != 1 ]]; then
  cat >"$results_root/summary.md" <<'EOF'
# krust versus canonical K/Haskell

Times are arithmetic means in seconds. Relative values are `krust / canonical`; values below 1 mean krust was faster.

| Suite | Case | Canonical mean | krust mean | krust / canonical |
|:--|:--|--:|--:|--:|
EOF
fi
for selected_suite in "${suites[@]}"; do
  configure_suite "$selected_suite"
  for selected_phase in "${phases[@]}"; do
    if [[ "$selected_phase" == compile ]]; then
      benchmark_pair "$selected_suite" compile
    elif [[ -n "$claim_override" ]]; then
      benchmark_pair "$selected_suite" prove "$claim_override"
    else
      for selected_claim in "${proof_claims[@]}"; do
        benchmark_pair "$selected_suite" prove "$selected_claim"
      done
    fi
  done
done

echo "benchmark results: $results_root"
