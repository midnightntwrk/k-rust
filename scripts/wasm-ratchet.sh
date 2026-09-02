#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"

k_checkout=${K_CHECKOUT:-"$workspace/k"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
log=${WASM_RATCHET_LOG:-"$workspace/draft/roadmap-tickets/phase-1/wasm-ratchet.log"}
timeout_seconds=${WASM_RATCHET_TIMEOUT_SECONDS:-1800}
memory_limit_kib=${WASM_RATCHET_MEMORY_KIB:-${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-6291456}}
rss_tolerance_percent=${WASM_RATCHET_RSS_TOLERANCE_PERCENT:-50}
label=
stage=
depth=

usage() {
  cat <<'EOF'
usage: scripts/wasm-ratchet.sh --label LABEL --stage EXPECTED_FAILURE_STAGE --depth N [--log PATH]

Run the pinned WASM test.md through the k-rust LLVM frontend and append a
machine-readable measurement to the Phase 1 ratchet log.

Failure stages, in monotone order:
  outer-parse
  configuration-parse
  rule-parse
  kompile-pass
  kore-emission

EXPECTED_FAILURE_STAGE is required for every probe because the outcome is not known
until after the command runs. It is replaced with "success" when the command exits
successfully. N is a nonnegative, operator-observed progress cursor within that
stage (for example, a stable source line or token offset). Use zero when no stable
cursor is visible; the log makes that loss of within-stage resolution explicit.

Peak RSS is compared with the most recent measured run at the same stage.
The default 50 percent tolerance can be changed with WASM_RATCHET_RSS_TOLERANCE_PERCENT.
EOF
}

die() {
  echo "error: $*" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --label)
      (($# >= 2)) || die "--label requires a value"
      label=$2
      shift 2
      ;;
    --stage)
      (($# >= 2)) || die "--stage requires a value"
      stage=$2
      shift 2
      ;;
    --depth)
      (($# >= 2)) || die "--depth requires a value"
      depth=$2
      shift 2
      ;;
    --log)
      (($# >= 2)) || die "--log requires a value"
      log=$2
      shift 2
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
[[ -n "$stage" ]] || die "--stage is required for a failing probe"
[[ "$depth" =~ ^[0-9]+$ ]] || die "--depth must be a nonnegative integer"
[[ "$timeout_seconds" =~ ^[1-9][0-9]*$ ]] || die "WASM_RATCHET_TIMEOUT_SECONDS must be positive"
[[ "$memory_limit_kib" =~ ^[1-9][0-9]*$ ]] || die "WASM_RATCHET_MEMORY_KIB must be positive"
[[ "$rss_tolerance_percent" =~ ^[0-9]+$ ]] || die "WASM_RATCHET_RSS_TOLERANCE_PERCENT must be nonnegative"

case "$stage" in
  outer-parse)
    stage_rank=0
    ;;
  configuration-parse)
    stage_rank=1
    ;;
  rule-parse)
    stage_rank=2
    ;;
  kompile-pass)
    stage_rank=3
    ;;
  kore-emission)
    stage_rank=4
    ;;
  *)
    die "unknown failure stage: $stage"
    ;;
esac

source_path="$wasm_checkout/pykwasm/src/pykwasm/kdist/wasm-semantics/test.md"
builtin_directory="$k_checkout/k-distribution/include/kframework/builtin"
[[ -f "$source_path" ]] || die "missing WASM source: $source_path"
[[ -d "$builtin_directory" ]] || die "missing K builtin directory: $builtin_directory"
[[ -d "$(dirname "$log")" ]] || die "log directory does not exist: $(dirname "$log")"
command -v python3 >/dev/null || die "python3 is required"
command -v jq >/dev/null || die "jq is required"
command -v sha256sum >/dev/null || die "sha256sum is required"
measure="$workspace/scripts/conformance/measure.py"
[[ -f "$measure" ]] || die "missing measurement helper: $measure"

reference_require_git_pin K "$k_checkout" "$K_REFERENCE_REVISION"
reference_require_git_pin WASM "$wasm_checkout" "$WASM_REFERENCE_REVISION"

krust=${WASM_RATCHET_KRUST:-}
if [[ -z "$krust" ]]; then
  cargo_bin=${CARGO:-cargo}
  command -v "$cargo_bin" >/dev/null || die "cargo is required"
  "$cargo_bin" build --quiet --release --manifest-path "$workspace/Cargo.toml" \
    -p k-rust --bin krust
  krust="$workspace/target/release/krust"
fi
[[ -x "$krust" ]] || die "krust executable is not executable: $krust"

work=$(mktemp -d "${TMPDIR:-/tmp}/k-rust-wasm-ratchet.XXXXXX")
lock=
cleanup() {
  if [[ -n "$lock" ]]; then
    rmdir "$lock" 2>/dev/null || true
  fi
  if [[ "${WASM_RATCHET_KEEP_WORK:-0}" == 1 ]]; then
    echo "WASM ratchet artifacts retained at: $work" >&2
  else
    find "$work" -depth -delete
  fi
}
trap cleanup EXIT

measurement="$work/measurement"
stderr="$measurement.stderr"
metrics="$measurement.meta.toml"
output_directory="$work/output"
mkdir "$output_directory"

set +e
(
  ulimit -v "$memory_limit_kib"
  exec python3 "$measure" --log "$measurement" --timeout "$timeout_seconds" -- \
    "$krust" kcompile "$source_path" \
      --main-module WASM-TEST \
      --backend llvm \
      --output-directory "$output_directory" \
      --emit-json \
      --builtin-directory "$builtin_directory"
)
measurement_status=$?
set -e
[[ -f "$metrics" ]] || die "measurement helper failed with exit $measurement_status"
exit_code=$(sed -n 's/^exit_code = //p' "$metrics")
timed_out=$(sed -n 's/^timed_out = //p' "$metrics")
wall_seconds=$(sed -n 's/^wall_seconds = //p' "$metrics")
peak_rss_kib=$(sed -n 's/^peak_rss_kib = //p' "$metrics")
[[ "$exit_code" =~ ^-?[0-9]+$ ]] || die "measurement helper recorded an invalid exit code"
[[ "$timed_out" == true || "$timed_out" == false ]] || die "measurement helper recorded an invalid timeout state"
[[ "$wall_seconds" =~ ^[0-9]+([.][0-9]+)?$ ]] || die "measurement helper recorded an invalid wall time"
[[ "$peak_rss_kib" =~ ^[0-9]+$ ]] || die "measurement helper recorded an invalid peak RSS"
peak_rss_measured=true
if [[ "$timed_out" == true ]]; then
  exit_code=124
fi
if ((exit_code == 0)); then
  stage=success
  stage_rank=5
  depth=0
fi

stderr_sha256=$(sha256sum "$stderr" | awk '{print $1}')
stderr_tail_json=$(tail -n 30 "$stderr" | jq -Rs .)
label_json=$(jq -Rn --arg value "$label" '$value')
timestamp_json=$(date -u +%Y-%m-%dT%H:%M:%SZ | jq -R .)
workspace_revision=$(git -C "$workspace" rev-parse HEAD)
workspace_revision_json=$(jq -Rn --arg value "$workspace_revision" '$value')
k_revision_json=$(jq -Rn --arg value "$K_REFERENCE_REVISION" '$value')
wasm_revision_json=$(jq -Rn --arg value "$WASM_REFERENCE_REVISION" '$value')
stage_json=$(jq -Rn --arg value "$stage" '$value')

lock="${log}.lock"
if ! mkdir "$lock" 2>/dev/null; then
  die "ratchet log is locked by another probe: $lock"
fi

previous_stage_rank=-1
previous_depth=-1
previous_peak_rss_kib=-1
sequence=0
if [[ -e "$log" ]]; then
  [[ -f "$log" ]] || die "ratchet log is not a regular file: $log"
  grep -Eq '^version = 1$' "$log" || die "ratchet log does not declare version 1: $log"
  sequence=$(awk '/^\[\[run\]\]$/ { count += 1 } END { print count + 0 }' "$log")
  read -r previous_stage_rank previous_depth < <(
    awk '
      /^stage_rank = [0-9]+$/ { rank = $3 }
      /^depth = [0-9]+$/ {
        candidate_depth = $3
        if (rank > best_rank || (rank == best_rank && candidate_depth > best_depth)) {
          best_rank = rank
          best_depth = candidate_depth
        }
      }
      END { print best_rank + 0, best_depth + 0 }
    ' best_rank=-1 best_depth=-1 "$log"
  )
  previous_peak_rss_kib=$(
    awk -v target_rank="$stage_rank" '
      /^stage_rank = [0-9]+$/ { rank = $3 }
      /^peak_rss_kib = [0-9]+$/ { peak = $3 }
      /^peak_rss_measured = true$/ {
        if (rank == target_rank) {
          latest = peak
        }
      }
      END { print latest + 0 }
    ' latest=-1 "$log"
  )
fi

regression=false
if ((stage_rank < previous_stage_rank)) || \
  ((stage_rank == previous_stage_rank && depth < previous_depth)); then
  regression=true
fi

rss_limit_kib=-1
rss_regression=false
if ((previous_peak_rss_kib >= 0)); then
  rss_limit_kib=$(((previous_peak_rss_kib * (100 + rss_tolerance_percent) + 99) / 100))
  if ((peak_rss_kib > rss_limit_kib)); then
    rss_regression=true
  fi
fi

entry="$work/entry"
{
  if [[ ! -e "$log" ]]; then
    printf 'version = 1\n'
  fi
  printf '\n[[run]]\n'
  printf 'sequence = %d\n' "$sequence"
  printf 'timestamp_utc = %s\n' "$timestamp_json"
  printf 'label = %s\n' "$label_json"
  printf 'workspace_revision = %s\n' "$workspace_revision_json"
  printf 'k_revision = %s\n' "$k_revision_json"
  printf 'wasm_revision = %s\n' "$wasm_revision_json"
  printf 'stage = %s\n' "$stage_json"
  printf 'stage_rank = %d\n' "$stage_rank"
  printf 'depth = %d\n' "$depth"
  printf 'previous_stage_rank = %d\n' "$previous_stage_rank"
  printf 'previous_depth = %d\n' "$previous_depth"
  printf 'regression = %s\n' "$regression"
  printf 'exit_code = %d\n' "$exit_code"
  printf 'timed_out = %s\n' "$timed_out"
  printf 'wall_seconds = %s\n' "$wall_seconds"
  printf 'peak_rss_kib = %d\n' "$peak_rss_kib"
  printf 'peak_rss_measured = %s\n' "$peak_rss_measured"
  printf 'previous_peak_rss_kib = %d\n' "$previous_peak_rss_kib"
  printf 'rss_tolerance_percent = %d\n' "$rss_tolerance_percent"
  printf 'rss_limit_kib = %d\n' "$rss_limit_kib"
  printf 'rss_regression = %s\n' "$rss_regression"
  printf 'stderr_sha256 = "%s"\n' "$stderr_sha256"
  printf 'stderr_tail = %s\n' "$stderr_tail_json"
} >"$entry"

if [[ -e "$log" ]]; then
  sed -n '/^\[\[run\]\]$/,$p' "$entry" >>"$log"
else
  cp "$entry" "$log"
fi

printf 'WASM ratchet: stage=%s depth=%s exit=%s wall=%ss rss=%sKiB rss-regression=%s log=%s\n' \
  "$stage" "$depth" "$exit_code" "$wall_seconds" "$peak_rss_kib" "$rss_regression" "$log"

if [[ "$regression" == true ]]; then
  echo "error: ratchet regression from stage rank $previous_stage_rank depth $previous_depth to stage rank $stage_rank depth $depth" >&2
  exit 3
fi
if [[ "$rss_regression" == true ]]; then
  echo "error: WASM ratchet RSS regression from ${previous_peak_rss_kib}KiB to ${peak_rss_kib}KiB (limit ${rss_limit_kib}KiB)" >&2
  exit 4
fi
if [[ "$timed_out" == true ]]; then
  echo "error: WASM probe timed out after ${timeout_seconds}s" >&2
  exit 124
fi
