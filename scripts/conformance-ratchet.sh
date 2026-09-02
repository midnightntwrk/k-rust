#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
helper="$workspace/scripts/conformance/ratchet.py"
measure="$workspace/scripts/conformance/measure.py"
summarize="$workspace/scripts/conformance/summarize.py"
driver=${CONFORMANCE_DRIVER:-"$workspace/scripts/conformance/run.py"}
expectations="$workspace/scripts/conformance/expectations.toml"
status="$workspace/draft/fable51-review/implementation-status.toml"
log="$workspace/draft/fable51-review/conformance-ratchet.toml"
runs_dir="$workspace/draft/fable51-review/conformance/runs"
jobs=2
label=
seed=
all=false
force=false
dry_run=false
cases=()
tickets=()
stages=()
original_args=("$@")

usage() {
  cat <<'EOF'
usage: scripts/conformance-ratchet.sh --label LABEL (--all | --cases NAME... | --ticket ID | --stage STAGE) [OPTIONS]
       scripts/conformance-ratchet.sh --seed RESULTS --label LABEL [OPTIONS]

Measure selected K regression-new cases, append their per-case ranks to the
standing ratchet, and fail with status 3 if a non-excluded rank decreases.

Options:
  --jobs N
  --log PATH
  --runs-dir PATH
  --expectations PATH
  --status PATH
  --force
  --dry-run
EOF
}

die() {
  echo "error: $*" >&2
  exit 2
}

require_value() {
  (($# >= 2)) || die "$1 requires a value"
}

while (($#)); do
  case "$1" in
    --label)
      require_value "$@"
      label=$2
      shift 2
      ;;
    --seed)
      require_value "$@"
      seed=$2
      shift 2
      ;;
    --cases)
      shift
      (($#)) || die "--cases requires at least one case"
      before=${#cases[@]}
      while (($#)) && [[ "$1" != --* ]]; do
        cases+=("$1")
        shift
      done
      ((${#cases[@]} > before)) || die "--cases requires at least one case"
      ;;
    --ticket)
      require_value "$@"
      tickets+=("$2")
      shift 2
      ;;
    --stage)
      require_value "$@"
      stages+=("$2")
      shift 2
      ;;
    --all)
      all=true
      shift
      ;;
    --jobs)
      require_value "$@"
      jobs=$2
      shift 2
      ;;
    --log)
      require_value "$@"
      log=$2
      shift 2
      ;;
    --runs-dir)
      require_value "$@"
      runs_dir=$2
      shift 2
      ;;
    --expectations)
      require_value "$@"
      expectations=$2
      shift 2
      ;;
    --status)
      require_value "$@"
      status=$2
      shift 2
      ;;
    --force)
      force=true
      shift
      ;;
    --dry-run)
      dry_run=true
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      die "unknown argument: $1"
      ;;
  esac
done

[[ -n "$label" ]] || die "--label is required"
[[ "$label" != *$'\n'* ]] || die "--label must be one line"
[[ "$jobs" =~ ^[1-9][0-9]*$ ]] || die "--jobs must be a positive integer"
[[ -f "$helper" ]] || die "missing ratchet helper: $helper"
[[ -f "$expectations" ]] || die "missing expectations: $expectations"
command -v python3 >/dev/null || die "python3 is required"

lock=
cleanup() {
  if [[ -n "$lock" ]]; then
    rmdir "$lock" 2>/dev/null || true
  fi
}
trap cleanup EXIT

acquire_lock() {
  lock="${log}.lock"
  mkdir -p "$(dirname "$log")"
  if ! mkdir "$lock" 2>/dev/null; then
    die "ratchet log is locked by another run: $lock"
  fi
}

if [[ -n "$seed" ]]; then
  [[ "$all" == false && ${#cases[@]} -eq 0 && ${#tickets[@]} -eq 0 && ${#stages[@]} -eq 0 ]] || \
    die "--seed cannot be combined with a run selection"
  [[ -f "$seed" ]] || die "missing seed results: $seed"
  acquire_lock
  exec_status=0
  python3 "$helper" seed \
    --results "$seed" \
    --expectations "$expectations" \
    --log "$log" \
    --label "$label" || exec_status=$?
  exit "$exec_status"
fi

if [[ "$all" == false && ${#cases[@]} -eq 0 && ${#tickets[@]} -eq 0 && ${#stages[@]} -eq 0 ]]; then
  die "select cases with --all, --cases, --ticket, or --stage"
fi

selection_args=(--expectations "$expectations")
if [[ "$all" == true ]]; then
  selection_args+=(--all)
fi
if ((${#cases[@]})); then
  selection_args+=(--cases "${cases[@]}")
fi
for ticket in "${tickets[@]}"; do
  selection_args+=(--ticket "$ticket")
done
for stage in "${stages[@]}"; do
  selection_args+=(--stage "$stage")
done
mapfile -t selected < <(python3 "$helper" select "${selection_args[@]}")
((${#selected[@]})) || die "the selection contains no conformance cases"

selection=all
if [[ "$all" == false ]]; then
  selection="cases=$(IFS=,; echo "${cases[*]}");tickets=$(IFS=,; echo "${tickets[*]}");stages=$(IFS=,; echo "${stages[*]}")"
fi

[[ -x "$driver" ]] || die "conformance driver is not executable: $driver"
[[ -f "$measure" ]] || die "missing measurement helper: $measure"
[[ -f "$summarize" ]] || die "missing summary helper: $summarize"
command -v jq >/dev/null || die "jq is required"
command -v sha256sum >/dev/null || die "sha256sum is required"

source "$workspace/scripts/reference-memory-guard.sh"
reference_enter_whole_job "${original_args[@]}"
source "$workspace/scripts/reference-pins.sh"

custom_driver=false
if [[ -n "${CONFORMANCE_DRIVER:-}" ]]; then
  custom_driver=true
fi
kompile=${K_KOMPILE:-"$workspace/k/result/bin/kompile"}
kore_parser=${K_KORE_PARSER:-"$(dirname "$kompile")/kore-parser"}
k_bin=$(dirname "$kompile")
k_checkout=${K_CHECKOUT:-"$workspace/k"}
if [[ "$custom_driver" == false || "${REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED:-0}" != 1 ]]; then
  [[ -x "$kompile" ]] || die "set K_KOMPILE to the pinned reference kompile executable"
  [[ -x "$kore_parser" ]] || die "set K_KORE_PARSER to the matching pinned kore-parser executable"
  reference_require_k_version "$kompile"
  reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"
fi

if [[ "$all" == true ]]; then
  if command -v agent-self >/dev/null; then
    echo "[conformance] memory envelope before the all-case run"
    agent-self
  fi
  if [[ "${CONFORMANCE_HEAVY_JOB_ACTIVE:-0}" == 1 && "$force" == false ]]; then
    die "another heavy job is declared active; retry alone or pass --force after checking agent-self"
  fi
fi

cargo_target_dir=${CARGO_TARGET_DIR:-"$workspace/target"}
krust=${CONFORMANCE_KRUST:-}
if [[ -z "$krust" ]]; then
  command -v cargo >/dev/null || die "cargo is required to build krust"
  echo "[conformance] building the release krust binary"
  cargo build --quiet --release --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust
  krust="$cargo_target_dir/release/krust"
fi
[[ -x "$krust" ]] || die "krust executable is not executable: $krust"

test_binary=${CONFORMANCE_TEST_BINARY:-}
if [[ -z "$test_binary" ]]; then
  echo "[conformance] building the reference comparison test binary"
  cargo test --quiet --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --test reference_differential --no-run
  newest_time=0
  for candidate in "$cargo_target_dir"/debug/deps/reference_differential-*; do
    [[ -x "$candidate" && "$candidate" != *.d ]] || continue
    candidate_time=$(stat -c %Y "$candidate")
    if ((candidate_time > newest_time)); then
      newest_time=$candidate_time
      test_binary=$candidate
    fi
  done
fi
[[ -x "$test_binary" ]] || die "reference comparison test binary is not executable: $test_binary"

driver_version=${CONFORMANCE_DRIVER_VERSION:-}
if [[ -z "$driver_version" ]]; then
  driver_version=$(git -C "$workspace" hash-object "$driver")
fi
krust_sha256=$(sha256sum "$krust" | awk '{print $1}')
test_binary_sha256=$(sha256sum "$test_binary" | awk '{print $1}')
workspace_revision=$(git -C "$workspace" rev-parse HEAD)

if [[ "$dry_run" == true ]]; then
  printf '[conformance] would run %d case(s):' "${#selected[@]}"
  printf ' %s' "${selected[@]}"
  printf '\n'
  exit 0
fi

acquire_lock
[[ -f "$log" ]] || die "seed entry 0 before running: $log"
sequence=$(python3 "$helper" next-sequence --log "$log")
label_slug=$(sed 's/[^A-Za-z0-9._-]/-/g' <<<"$label")
[[ -n "$label_slug" ]] || die "--label must contain a path-safe character"
mkdir -p "$runs_dir"
run_dir="$runs_dir/$sequence-$label_slug"
if ! mkdir "$run_dir" 2>/dev/null; then
  die "run artifact directory already exists: $run_dir"
fi
results="$run_dir/results.toml"
logs="$run_dir/logs"
mkdir "$logs"

driver_args=(
  --workspace "$workspace"
  --k-bin "$k_bin"
  --krust "$krust"
  --test-binary "$test_binary"
  --kore-parser "$kore_parser"
  --work-tree "${CONFORMANCE_WORK_TREE:-/tmp/k-rust-conformance/k-distribution}"
  --results "$results"
  --logs "$logs"
  --expectations "$expectations"
  --jobs "$jobs"
  --cases "${selected[@]}"
)
driver_command=("$driver")
if [[ "$driver" == *.py ]]; then
  driver_command=(python3 "$driver")
fi

echo "[conformance] measuring ${#selected[@]} case(s) into $run_dir"
set +e
python3 "$measure" --log "$run_dir/driver" -- \
  "${driver_command[@]}" "${driver_args[@]}"
driver_status=$?
set -e
if [[ -f "$run_dir/driver.stdout" ]]; then
  cat "$run_dir/driver.stdout"
fi
if ((driver_status != 0)); then
  cat "$run_dir/driver.stderr" >&2
  echo "error: conformance driver exited $driver_status; ratchet log was not changed" >&2
  exit "$driver_status"
fi
[[ -f "$results" ]] || die "conformance driver did not produce results: $results"

python3 "$summarize" "$results" "$run_dir/summary.md"
wall_seconds=$(sed -n 's/^wall_seconds = //p' "$run_dir/driver.meta.toml")
peak_rss_mib=$(sed -n 's/^peak_rss_mib = //p' "$run_dir/driver.meta.toml")
[[ "$wall_seconds" =~ ^[0-9]+([.][0-9]+)?$ ]] || die "measurement has no wall_seconds"
[[ "$peak_rss_mib" =~ ^[0-9]+$ ]] || die "measurement has no peak_rss_mib"

append_status=0
python3 "$helper" append \
  --results "$results" \
  --expectations "$expectations" \
  --status "$status" \
  --log "$log" \
  --label "$label" \
  --workspace-revision "$workspace_revision" \
  --k-revision "$K_REFERENCE_REVISION" \
  --driver-version "$driver_version" \
  --krust-sha256 "$krust_sha256" \
  --test-binary-sha256 "$test_binary_sha256" \
  --selection "$selection" \
  --jobs "$jobs" \
  --wall-seconds "$wall_seconds" \
  --peak-rss-mib "$peak_rss_mib" \
  --artifacts "$run_dir" || append_status=$?
exit "$append_status"
