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
BENCHMARK_MEMORY_METHOD=${BENCHMARK_MEMORY_METHOD:-auto}

usage() {
  cat <<'EOF'
Usage: scripts/benchmark.sh [OPTIONS]

Compare release-mode krust with canonical K's Haskell backend.

Options:
  --suite imp|kevm|all       Benchmark suite (default: all)
  --phase compile|spec-compile|load|execute|prove|all
                              Benchmark phase (default: all)
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

Peak memory of each run's whole process tree is recorded when a user systemd
manager can delegate a cgroup v2 scope; otherwise it is reported as unknown.
Set BENCHMARK_MEMORY_METHOD=none to skip it.
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
      --for-proving
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

prepare_krust_proof() {
  local work=$1
  local output="$work/krust-definition"
  reset_output "$output"
  rust_args=(
    "$KRUST_BIN" kcompile "$compile_source"
    --main-module "$compile_main"
    --syntax-module "$compile_syntax"
    --for-proving
    --output-directory "$output"
    --builtin-directory "$K_CHECKOUT/k-distribution/include/kframework/builtin"
  )
  append_source_args rust
  [[ -z "$hook_namespaces" ]] || rust_args+=(--hook-namespaces "$hook_namespaces")
  [[ -z "$markdown_selector" ]] || rust_args+=(--md-selector "$markdown_selector")
  "${rust_args[@]}"
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
      --compiled-definition "$work/krust-definition"
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

run_spec_compile() {
  local work=$1
  rust_args=(
    "$KRUST_BIN" kcompile "$specification"
    --compiled-definition "$work/krust-definition"
    --main-module "$spec_module"
    --definition-module "$definition_module"
    --for-proving
    --output-directory "$work/krust-specification"
    --builtin-directory "$K_CHECKOUT/k-distribution/include/kframework/builtin"
  )
  append_source_args rust
  [[ -z "$hook_namespaces" ]] || rust_args+=(--hook-namespaces "$hook_namespaces")
  [[ -z "$markdown_selector" ]] || rust_args+=(--md-selector "$markdown_selector")
  "${rust_args[@]}"
}

run_execute() {
  local work=$1
  local claim=$2
  local timing_file=${3:-}
  rust_args=(
    "$KRUST_BIN" kprove
    --compiled-definition "$work/krust-specification"
    --main-module "$spec_module"
    --claim "$claim"
    --depth "$proof_depth"
  )
  [[ -z "$timing_file" ]] || rust_args+=(--timings "$timing_file")
  "${rust_args[@]}"
}

run_load() {
  local work=$1
  "$KRUST_BIN" kprove \
    --compiled-definition "$work/krust-specification" \
    --main-module "$spec_module" \
    --load-only
}

tree_memory_description='cgroup v2 memory.peak of a fresh per-run cgroup that holds the whole process tree of the command'
# hyperfine's memory_usage_byte behaves as getrusage(RUSAGE_CHILDREN).ru_maxrss:
# the largest single process among everything hyperfine has reaped so far.
# With hyperfine 1.20, `true` benchmarked after a command that allocates
# 300 MiB reports that command's 309 MiB. It is neither a sum over the tree
# nor specific to one command, so it stays in results.json as hyperfine wrote
# it but is not reported.
hyperfine_memory_note='not reported: it is the largest single process hyperfine has reaped so far (getrusage RUSAGE_CHILDREN), so it is neither a sum over the process tree nor specific to the run or the command'

# A benchmark started inside a memory-limited scope would otherwise escape
# that limit by starting its own scope, so the tightest limits of the current
# cgroup and its ancestors are copied onto the new scope.
inherited_scope_properties() {
  local current
  local directory
  local key
  local limit
  local value
  current=/sys/fs/cgroup$(cut -d: -f3- /proc/self/cgroup 2>/dev/null | head -n 1)
  for key in max high swap.max; do
    limit=
    directory=$current
    while [[ "$directory" == /sys/fs/cgroup/* ]]; do
      if [[ -r "$directory/memory.$key" ]]; then
        read -r value <"$directory/memory.$key"
        if [[ "$value" =~ ^[0-9]+$ ]] && [[ -z "$limit" || "$value" -lt "$limit" ]]; then
          limit=$value
        fi
      fi
      directory=${directory%/*}
    done
    [[ -n "$limit" ]] || continue
    case "$key" in
      max) echo "MemoryMax=$limit" ;;
      high) echo "MemoryHigh=$limit" ;;
      swap.max) echo "MemorySwapMax=$limit" ;;
    esac
  done
}

memory_scope_properties() {
  local property
  scope_properties=(-p Delegate=yes)
  while read -r property; do
    scope_properties+=(-p "$property")
  done < <(inherited_scope_properties)
}

# Runs inside a delegated scope: moves this shell into a supervisor child so
# the scope may enable the memory controller for its children, then creates
# one empty cgroup per expected run. Creating them here keeps mkdir out of the
# timed region.
enter_memory_scope() {
  local count=$1
  local index
  memory_scope=/sys/fs/cgroup$(cut -d: -f3- /proc/self/cgroup | head -n 1)
  [[ -w "$memory_scope/cgroup.procs" ]] || return 1
  mkdir "$memory_scope/supervisor" || return 1
  echo $$ >"$memory_scope/supervisor/cgroup.procs" || return 1
  echo +memory >"$memory_scope/cgroup.subtree_control" || return 1
  for ((index = 1; index <= count; index++)); do
    mkdir "$memory_scope/run-$index" || return 1
  done
  [[ -r "$memory_scope/run-1/memory.peak" && -r "$memory_scope/run-1/memory.stat" ]]
}

leave_memory_scope() {
  local directory
  for directory in "$memory_scope"/run-*; do
    [[ ! -d "$directory" ]] || rmdir "$directory" 2>/dev/null || true
  done
}

tree_memory_available() {
  [[ "$BENCHMARK_MEMORY_METHOD" != none ]] || return 1
  command -v systemd-run >/dev/null 2>&1 || return 1
  memory_scope_properties
  systemd-run --user --scope --quiet "${scope_properties[@]}" -- \
    "$BASH" "$script" __memory-probe >/dev/null 2>&1
}

# The per-run cgroup is chosen in hyperfine's --prepare step, outside the
# timed region: the prepare step moves hyperfine itself into the next empty
# run cgroup, so the command hyperfine then forks starts there and no process
# changes cgroup while it is timed. (Moving a process can wait for an RCU
# grace period, several milliseconds on a busy host.) The same step first
# records the previous run's peak, once every process of that run has exited.
memory_record_current() {
  local index
  local engine
  local run_cgroup
  local peak=unknown
  local page_cache=unknown
  local key
  local value
  [[ -f "$BENCHMARK_MEMORY_DIR/current" ]] || return 0
  read -r index engine <"$BENCHMARK_MEMORY_DIR/current"
  rm -f "$BENCHMARK_MEMORY_DIR/current"
  run_cgroup=$BENCHMARK_MEMORY_CGROUP/run-$index
  [[ ! -r "$run_cgroup/memory.peak" ]] || read -r peak <"$run_cgroup/memory.peak"
  if [[ -r "$run_cgroup/memory.stat" ]]; then
    while read -r key value; do
      [[ "$key" != file ]] || page_cache=$value
    done <"$run_cgroup/memory.stat"
  fi
  printf '%s\t%s\t%s\n' "$index" "$peak" "$page_cache" >>"$BENCHMARK_MEMORY_DIR/$engine.tsv"
}

memory_prepare() {
  local engine=$1
  local index
  local hyperfine_pid
  memory_record_current
  read -r index <"$BENCHMARK_MEMORY_DIR/next-run"
  index=$((index + 1))
  echo "$index" >"$BENCHMARK_MEMORY_DIR/next-run"
  read -r hyperfine_pid <"$BENCHMARK_MEMORY_DIR/hyperfine-pid"
  if [[ -d "$BENCHMARK_MEMORY_CGROUP/run-$index" ]] && \
    { echo "$hyperfine_pid" >"$BENCHMARK_MEMORY_CGROUP/run-$index/cgroup.procs"; } 2>/dev/null; then
    echo "$index $engine" >"$BENCHMARK_MEMORY_DIR/current"
  else
    printf '%s\tunknown\tunknown\n' "$index" >>"$BENCHMARK_MEMORY_DIR/$engine.tsv"
  fi
}

# Prints the --prepare command for one engine: the move into the next run
# cgroup when memory is measured, then the existing preparation, if any. The
# move comes first so the previous run's page cache is read before the
# preparation deletes its output; the preparation's own processes descend
# from a shell forked before the move and stay in the previous run's cgroup.
prepare_with_memory() {
  local engine=$1
  local existing=$2
  local move
  if [[ "$tree_memory" != 1 ]]; then
    printf '%s' "$existing"
    return
  fi
  move=$(shell_command "$script" __memory-prepare "$engine")
  if [[ -n "$existing" ]]; then
    printf '%s && %s' "$move" "$existing"
  else
    printf '%s' "$move"
  fi
}

run_hyperfine() {
  local result_dir=$1
  local total_runs=$2
  shift 2
  if [[ "$tree_memory" == 1 ]]; then
    if [[ -e "$result_dir/memory" ]]; then
      find "$result_dir/memory" -depth -delete
    fi
    mkdir -p "$result_dir/memory"
    printf 'memory: each run is prepared by %s ENGINE, which records the previous run and moves hyperfine into the next run cgroup\n' \
      "$(shell_command "$script" __memory-prepare)" >>"$result_dir/commands.txt"
    memory_scope_properties
    systemd-run --user --scope --quiet "${scope_properties[@]}" -- \
      "$BASH" "$script" __memory-scope "$result_dir/memory" "$total_runs" "$HYPERFINE" "$@"
  else
    "$HYPERFINE" "$@"
  fi
}

# Adds the memory figures to hyperfine's results.json. Warmup samples are
# dropped: hyperfine runs each command's warmups immediately before its timed
# runs, and each engine writes its own sample file. A sample set whose length
# is not the run count, or that holds an unknown sample, is reported as null.
record_memory() {
  local result_dir=$1
  local warmup=$2
  local runs=$3
  local result_json=$result_dir/results.json
  local canonical_samples=
  local rust_samples=
  local tree_method=unknown
  local temporary
  if [[ "$tree_memory" == 1 ]]; then
    tree_method=$tree_memory_description
    [[ ! -f "$result_dir/memory/canonical-haskell.tsv" ]] || canonical_samples=$(<"$result_dir/memory/canonical-haskell.tsv")
    [[ ! -f "$result_dir/memory/krust.tsv" ]] || rust_samples=$(<"$result_dir/memory/krust.tsv")
  fi
  temporary=$(mktemp "$result_dir/results.json.XXXXXX")
  jq \
    --arg canonical_samples "$canonical_samples" \
    --arg rust_samples "$rust_samples" \
    --argjson warmup "$warmup" \
    --argjson runs "$runs" \
    --arg tree_method "$tree_method" \
    --arg hyperfine_note "$hyperfine_memory_note" \
    '
    def median:
      sort | length as $n
      | if $n == 0 then null
        elif $n % 2 == 1 then .[($n - 1) / 2]
        else (.[$n / 2 - 1] + .[$n / 2]) / 2
        end;
    def samples($raw):
      [$raw | split("\n")[] | select(length > 0) | split("\t")]
      | .[$warmup:]
      | if length == $runs and all(.[]; (.[1] | test("^[0-9]+$")) and (.[2] | test("^[0-9]+$")))
        then {peak: map(.[1] | tonumber), cache: map(.[2] | tonumber)}
        else null
        end;
    def ratio($a; $b): if $a == null or $b == null or $b == 0 then null else $a / $b end;
    ({"canonical-haskell": samples($canonical_samples), krust: samples($rust_samples)}) as $tree
    | .results |= map(
        . as $result
        | ($tree[$result.command]) as $s
        | .peak_memory = {
            tree_peak_bytes: ($s.peak // null),
            tree_peak_median_bytes: (if $s == null then null else ($s.peak | median) end),
            tree_peak_max_bytes: (if $s == null then null else ($s.peak | max) end),
            tree_page_cache_at_exit_bytes: ($s.cache // null)
          }
      )
    | .memory_method = {
        tree_peak: $tree_method,
        hyperfine_memory_usage_byte: $hyperfine_note
      }
    | ([.results[] | select(.command == "canonical-haskell")][0]) as $canonical
    | ([.results[] | select(.command == "krust")][0]) as $rust
    | if $canonical == null or $rust == null then .
      else .speedup = ratio($canonical.mean; $rust.mean)
      | .krust_over_canonical = {
          mean_time: ratio($rust.mean; $canonical.mean),
          tree_peak_median: ratio($rust.peak_memory.tree_peak_median_bytes; $canonical.peak_memory.tree_peak_median_bytes)
        }
      end
    ' "$result_json" >"$temporary"
  mv "$temporary" "$result_json"
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
  if [[ -n "$claim" ]]; then
    shell_command "$script" __run "$phase" "$engine" "$suite" "$work" "$claim"
  else
    shell_command "$script" __run "$phase" "$engine" "$suite" "$work"
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
    --argjson rust_dirty "$([[ -n "$(git -C "$workspace" status --porcelain --untracked-files=no)" ]] && echo true || echo false)" \
    --arg k_revision "$(git -C "$K_CHECKOUT" rev-parse HEAD)" \
    --arg semantics_revision "$(git -C "$source_checkout" rev-parse HEAD)" \
    --arg krust_version "$($KRUST_BIN --version)" \
    --arg rustc_version "$(rustc --version 2>/dev/null || echo unavailable)" \
    --arg canonical_version "$canonical_version" \
    --arg hyperfine_version "$($HYPERFINE --version)" \
    --arg ghcrts "$GHCRTS" \
    --arg k_opts "$REFERENCE_K_OPTS" \
    --arg memory_method "$([[ "$tree_memory" == 1 ]] && echo "$tree_memory_description" || echo unknown)" \
    '{
      suite: $suite,
      phase: $phase,
      timestamp: $timestamp,
      host: {system: $system, cpu: $cpu, memory_bytes: $memory_bytes},
      revisions: {krust: $rust_revision, krust_dirty: $rust_dirty, k: $k_revision, semantics: $semantics_revision},
      tools: {krust: $krust_version, rustc: $rustc_version, canonical: $canonical_version, hyperfine: $hyperfine_version},
      environment: {GHCRTS: $ghcrts, K_OPTS: $k_opts},
      memory_method: $memory_method
    }' >"$result_dir/metadata.json"
}

# Memory cells in MiB: "median (max)" of the timed runs, or unknown.
summary_memory_jq='
  def mib: . / 1048576 | . * 10 | round / 10 | tostring | if test("\\.") then . else . + ".0" end;
  def cell($m; $median; $max):
    if $m == null or $m[$median] == null then "unknown"
    else "\($m[$median] | mib) (\($m[$max] | mib))"
    end;
  def ratio_cell($value): if $value == null then "unknown" else $value | tostring end;
  def result($name): [.results[] | select(.command == $name)][0];
'

append_summary() {
  local suite=$1
  local case_name=$2
  local result_json=$3
  local row
  row=$(jq -r --arg suite "$suite" --arg case_name "$case_name" "$summary_memory_jq"'
    (result("canonical-haskell")) as $canonical
    | (result("krust")) as $rust
    | [
        $suite,
        $case_name,
        ($canonical.mean | tostring),
        ($rust.mean | tostring),
        ($canonical.mean / $rust.mean | tostring),
        cell($canonical.peak_memory; "tree_peak_median_bytes"; "tree_peak_max_bytes"),
        cell($rust.peak_memory; "tree_peak_median_bytes"; "tree_peak_max_bytes"),
        ratio_cell(.krust_over_canonical.tree_peak_median)
      ]
    | @tsv
  ' "$result_json")
  IFS=$'\t' read -r row_suite row_case canonical_mean rust_mean speedup \
    canonical_tree rust_tree tree_relative <<<"$row"
  [[ "$tree_relative" == unknown ]] || printf -v tree_relative '%.2fx' "$tree_relative"
  # Time is reported as a speedup, canonical / krust, so the cell says how many times faster
  # krust is; a case where krust is slower says so with the inverse factor.
  if awk -v s="$speedup" 'BEGIN { exit !(s >= 1) }'; then
    printf -v speedup '%.2fx faster' "$speedup"
  else
    speedup=$(awk -v s="$speedup" 'BEGIN { printf "%.2fx slower", 1 / s }')
  fi
  printf '| %s | %s | %.3f | %.3f | %s | %s | %s | %s |\n' \
    "$row_suite" "$row_case" "$canonical_mean" "$rust_mean" "$speedup" \
    "$canonical_tree" "$rust_tree" "$tree_relative" \
    >>"$results_root/summary.md"
}

default_runs() {
  case "$1:$2" in
    compile:imp) echo 3 ;;
    compile:kevm) echo 1 ;;
    spec-compile:imp) echo 3 ;;
    spec-compile:kevm) echo 1 ;;
    load:imp) echo 5 ;;
    load:kevm) echo 3 ;;
    prove:imp) echo 5 ;;
    prove:kevm) echo 3 ;;
    execute:imp) echo 5 ;;
    execute:kevm) echo 3 ;;
  esac
}

default_warmup() {
  case "$1:$2" in
    load:*|prove:*|execute:*) echo 1 ;;
    *) echo 0 ;;
  esac
}

append_single_summary() {
  local suite=$1
  local case_name=$2
  local result_json=$3
  local row
  row=$(jq -r "$summary_memory_jq"'
    (result("krust")) as $rust
    | [
        ($rust.mean | tostring),
        cell($rust.peak_memory; "tree_peak_median_bytes"; "tree_peak_max_bytes")
      ]
    | @tsv
  ' "$result_json")
  IFS=$'\t' read -r rust_mean rust_tree <<<"$row"
  printf '| %s | %s | — | %.3f | — | — | %s | — |\n' "$suite" "$case_name" "$rust_mean" "$rust_tree" \
    >>"$results_root/summary.md"
}

benchmark_single() {
  local suite=$1
  local phase=$2
  local claim=${3:-}
  local case_name=$phase
  [[ -z "$claim" ]] || case_name="$phase-${claim##*.}"
  local result_dir="$results_root/$suite/$case_name"
  local work="$BENCHMARK_WORK_ROOT/$suite"
  local selected_runs=${runs_override:-$(default_runs "$phase" "$suite")}
  local selected_warmup=${warmup_override:-$(default_warmup "$phase" "$suite")}
  local rust_command
  local rust_prepare
  rust_command=$(command_for "$phase" krust "$suite" "$work" "$claim")
  mkdir -p "$result_dir" "$work"
  printf 'krust: %s\n' "$rust_command" >"$result_dir/commands.txt"
  if [[ "$dry_run" == 1 ]]; then
    echo "[$suite:$case_name]"
    cat "$result_dir/commands.txt"
    return
  fi
  if [[ ! -f "$work/krust-definition/krust.json" || ! -f "$work/krust-definition/parsed.provenance.json" ]]; then
    echo "[$suite] preparing proof-ready krust definition"
    "$script" __prepare-krust-proof "$suite" "$work"
  fi
  if [[ "$phase" != spec-compile && ! -f "$work/krust-specification/krust.json" ]]; then
    echo "[$suite] compiling the specification against prepared semantics"
    run_spec_compile "$work"
  fi
  if [[ "$skip_preflight" != 1 ]]; then
    echo "[$suite:$case_name] correctness preflight"
    "$script" __check "$phase" krust "$suite" "$work" "$claim" >"$result_dir/krust-preflight.log" 2>&1
  fi
  write_metadata "$suite" "$case_name" "$result_dir"
  echo "[$suite:$case_name] benchmarking $selected_runs run(s), $selected_warmup warmup(s)"
  hyperfine_args=(
    --style basic
    --runs "$selected_runs"
    --warmup "$selected_warmup"
  )
  rust_prepare=$(prepare_with_memory krust "")
  [[ -z "$rust_prepare" ]] || hyperfine_args+=(--prepare "$rust_prepare")
  run_hyperfine "$result_dir" $((selected_runs + selected_warmup)) "${hyperfine_args[@]}" \
    --command-name krust "$rust_command" \
    --export-json "$result_dir/results.json" \
    --export-markdown "$result_dir/results.md"
  record_memory "$result_dir" "$selected_warmup" "$selected_runs"
  append_single_summary "$suite" "$case_name" "$result_dir/results.json"
  if [[ "$phase" == execute ]]; then
    # A separate instrumented run measures prove_claim directly, not by subtracting load times.
    run_execute "$work" "$claim" "$result_dir/phase-timings.json" >"$result_dir/timed-proof.log" 2>&1
  fi
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
  if [[ "$phase" == prove && ( ! -f "$work/krust-definition/krust.json" || ! -f "$work/krust-definition/parsed.provenance.json" ) ]]; then
    echo "[$suite] preparing proof-ready krust definition"
    "$script" __prepare-krust-proof "$suite" "$work"
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
  canonical_prepare=$(prepare_with_memory canonical-haskell "$canonical_prepare")
  rust_prepare=$(prepare_with_memory krust "$rust_prepare")
  [[ -z "$canonical_prepare" ]] || hyperfine_args+=(--prepare "$canonical_prepare")
  [[ -z "$rust_prepare" ]] || hyperfine_args+=(--prepare "$rust_prepare")
  run_hyperfine "$result_dir" $((2 * (selected_runs + selected_warmup))) "${hyperfine_args[@]}" \
    --command-name canonical-haskell "$canonical_command" \
    --command-name krust "$rust_command" \
    --export-json "$result_dir/results.json" \
    --export-markdown "$result_dir/results.md"
  record_memory "$result_dir" "$selected_warmup" "$selected_runs"
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
  case "$internal_phase" in
    compile) run_compile "$internal_engine" "$internal_work" ;;
    load) run_load "$internal_work" ;;
    spec-compile) run_spec_compile "$internal_work" ;;
    execute) run_execute "$internal_work" "$internal_claim" ;;
    prove) run_proof "$internal_engine" "$internal_claim" "$internal_work" ;;
    *) fail "unknown internal benchmark phase: $internal_phase" ;;
  esac
  exit
fi

if [[ "${1:-}" == __memory-probe ]]; then
  enter_memory_scope 1
  status=$?
  leave_memory_scope
  exit "$status"
fi

if [[ "${1:-}" == __memory-scope ]]; then
  shift
  memory_dir=$1
  memory_runs=$2
  shift 2
  if enter_memory_scope "$memory_runs"; then
    echo 0 >"$memory_dir/next-run"
    export BENCHMARK_MEMORY_CGROUP=$memory_scope BENCHMARK_MEMORY_DIR=$memory_dir
  else
    echo "warning: could not create per-run memory cgroups; tree peak memory is unknown for this case" >&2
  fi
  status=0
  # The subshell records its own PID and becomes hyperfine, so the prepare
  # step knows which process to move.
  (
    echo "$BASHPID" >"$memory_dir/hyperfine-pid"
    exec "$@"
  ) || status=$?
  [[ -z "${BENCHMARK_MEMORY_CGROUP:-}" ]] || memory_record_current
  leave_memory_scope
  exit "$status"
fi

if [[ "${1:-}" == __memory-prepare ]]; then
  [[ -n "${BENCHMARK_MEMORY_CGROUP:-}" ]] || exit 0
  memory_prepare "$2"
  exit
fi

if [[ "${1:-}" == __prepare-proof ]]; then
  shift
  BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:?}
  configure_suite "$1"
  prepare_proof "$2"
  exit
fi

if [[ "${1:-}" == __prepare-krust-proof ]]; then
  shift
  BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:?}
  configure_suite "$1"
  prepare_krust_proof "$2"
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
  elif [[ "$internal_phase" == load ]]; then
    run_load "$internal_work"
  elif [[ "$internal_phase" == spec-compile ]]; then
    run_spec_compile "$internal_work"
  elif [[ "$internal_engine" == krust ]]; then
    proof_status=0
    if [[ "$internal_phase" == execute ]]; then
      proof_output=$(run_execute "$internal_work" "$internal_claim" 2>&1) || proof_status=$?
    else
      proof_output=$(run_proof "$internal_engine" "$internal_claim" "$internal_work" 2>&1) || proof_status=$?
    fi
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
case "$phase" in compile|spec-compile|load|execute|prove|all) ;; *) fail "unknown --phase: $phase" ;; esac
[[ -z "$runs_override" || "$runs_override" =~ ^[1-9][0-9]*$ ]] || fail "--runs must be positive"
[[ -z "$warmup_override" || "$warmup_override" =~ ^[0-9]+$ ]] || fail "--warmup must be non-negative"
if [[ -n "$claim_override" ]]; then
  [[ "$suite" != all ]] || fail "--claim requires --suite imp or --suite kevm"
  [[ "$phase" == prove || "$phase" == execute || "$phase" == all ]] || fail "--claim requires a proof phase"
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
imp/spec-compile
imp/load
imp/execute/IMP-SIMPLE-SPEC.addition-var
imp/execute/IMP-SIMPLE-SPEC.branching-program
imp/execute/IMP-SIMPLE-SPEC.sum-loop
imp/prove/IMP-SIMPLE-SPEC.addition-var
imp/prove/IMP-SIMPLE-SPEC.branching-program
imp/prove/IMP-SIMPLE-SPEC.sum-loop
kevm/compile
kevm/spec-compile
kevm/load
kevm/execute/SLOT-UPDATES-SPEC.gfob-min
kevm/prove/SLOT-UPDATES-SPEC.gfob-min
EOF
  exit
fi

if [[ -z "$results_root" ]]; then
  results_root="$workspace/target/benchmarks/results/$(date -u +%Y%m%dT%H%M%SZ)"
elif [[ "$results_root" != /* ]]; then
  results_root="$workspace/$results_root"
fi
BENCHMARK_WORK_ROOT=${BENCHMARK_WORK_ROOT:-"$workspace/target/benchmarks/work"}
[[ "$BENCHMARK_WORK_ROOT" == /* ]] || BENCHMARK_WORK_ROOT="$workspace/$BENCHMARK_WORK_ROOT"
export K_CHECKOUT IMP_SEMANTICS_CHECKOUT EVM_SEMANTICS_CHECKOUT KRUST_BIN K_KOMPILE K_KPROVE
export HYPERFINE REFERENCE_K_OPTS GHCRTS BENCHMARK_WORK_ROOT

suites=()
phases=()
if [[ "$suite" == all ]]; then suites=(imp kevm); else suites=("$suite"); fi
if [[ "$phase" == all ]]; then phases=(compile spec-compile load execute prove); else phases=("$phase"); fi

if [[ "$dry_run" != 1 ]]; then
  command -v jq >/dev/null 2>&1 || fail "jq is required to record benchmark metadata"
  for selected_suite in "${suites[@]}"; do
    check_tools_and_sources "$selected_suite"
  done
fi

tree_memory=0
if [[ "$dry_run" != 1 ]] && tree_memory_available; then
  tree_memory=1
fi
export BENCHMARK_MEMORY_METHOD

mkdir -p "$results_root"
if [[ "$dry_run" != 1 ]]; then
  heap_limit=$(grep -o -- '-Xmx[^[:space:]]*' <<<"$REFERENCE_K_OPTS" | tail -n 1 || true)
  if [[ "$tree_memory" == 1 ]]; then
    tree_method_text="Peak memory is the ${tree_memory_description}: every process the command starts, including the JVM's backend children, is charged to that cgroup, so processes resident at the same time are summed. The figure is resident anonymous and kernel memory plus the page cache the run itself brings in (files it reads that were not cached yet and files it writes); \`results.json\` records that page cache at exit as \`tree_page_cache_at_exit_bytes\`. File pages already in the page cache when the run starts, such as the executables, shared libraries and JARs after the first run, stay charged to the cgroup that first read them and are not counted."
  else
    tree_method_text="Peak memory of the process tree is unknown: this host could not start a delegated user systemd scope with the cgroup v2 memory controller (or BENCHMARK_MEMORY_METHOD=none)."
  fi
  cat >"$results_root/summary.md" <<EOF
# krust versus canonical K/Haskell

Times are arithmetic means in seconds. The speedup is \`canonical / krust\` mean time: how many times faster krust is (a case where krust is slower says "slower" with the inverse factor). The memory ratio is \`krust / canonical\` median peak: the fraction of canonical's memory krust uses.

${tree_method_text}
Memory cells are the median over the timed runs, with the maximum in parentheses, in MiB; the memory ratio compares medians.
hyperfine's own \`memory_usage_byte\` in \`results.json\` is not used: it is the largest single process hyperfine has reaped so far, so it neither sums a JVM and its backend children nor keeps one command's runs apart from the other's.

The canonical JVM runs with \`K_OPTS=${REFERENCE_K_OPTS}\`, so its heap limit is ${heap_limit:-the JVM default}.
A JVM grows its heap toward that limit before it collects hard, so the canonical peak reflects the limit as well as the data the workload keeps live; a smaller limit could lower it at some cost in time, and the benchmark does not tune it for either side.

| Suite | Case | Canonical mean | krust mean | krust speedup | Canonical peak MiB | krust peak MiB | krust / canonical peak |
|:--|:--|--:|--:|--:|--:|--:|--:|
EOF
fi
for selected_suite in "${suites[@]}"; do
  configure_suite "$selected_suite"
  for selected_phase in "${phases[@]}"; do
    if [[ "$selected_phase" == compile ]]; then
      benchmark_pair "$selected_suite" compile
    elif [[ "$selected_phase" == load || "$selected_phase" == spec-compile ]]; then
      benchmark_single "$selected_suite" "$selected_phase"
    elif [[ "$selected_phase" == execute ]]; then
      if [[ -n "$claim_override" ]]; then
        benchmark_single "$selected_suite" execute "$claim_override"
      else
        for selected_claim in "${proof_claims[@]}"; do
          benchmark_single "$selected_suite" execute "$selected_claim"
        done
      fi
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
