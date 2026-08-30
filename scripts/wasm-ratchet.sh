#!/usr/bin/env bash
set -euo pipefail

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
source "$workspace/scripts/reference-pins.sh"

k_checkout=${K_CHECKOUT:-"$workspace/k"}
wasm_checkout=${WASM_SEMANTICS_CHECKOUT:-"$workspace/wasm-semantics"}
log=${WASM_RATCHET_LOG:-"$workspace/draft/roadmap-tickets/phase-1/wasm-ratchet.log"}
timeout_seconds=${WASM_RATCHET_TIMEOUT_SECONDS:-1800}
memory_limit_kib=${WASM_RATCHET_MEMORY_KIB:-${REFERENCE_DIFFERENTIAL_MEMORY_KIB:-6291456}}
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
command -v timeout >/dev/null || die "timeout is required"
command -v jq >/dev/null || die "jq is required"
command -v sha256sum >/dev/null || die "sha256sum is required"

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

stdout="$work/stdout"
stderr="$work/stderr"
metrics="$work/metrics"
output_directory="$work/output"
mkdir "$output_directory"

time_bin=${WASM_RATCHET_TIME:-}
if [[ -z "$time_bin" ]] && command -v gtime >/dev/null; then
  time_bin=$(command -v gtime)
elif [[ -z "$time_bin" && -x /usr/bin/time ]]; then
  time_bin=/usr/bin/time
fi
if [[ -n "$time_bin" && ! -x "$time_bin" ]]; then
  die "WASM_RATCHET_TIME is not executable: $time_bin"
fi

started=$EPOCHREALTIME
set +e
(
  ulimit -v "$memory_limit_kib"
  if [[ -n "$time_bin" ]]; then
    timeout --kill-after=30s "${timeout_seconds}s" \
      "$time_bin" -f 'peak_rss_kib=%M' -o "$metrics" \
      "$krust" kcompile "$source_path" \
        --main-module WASM-TEST \
        --backend llvm \
        --output-directory "$output_directory" \
        --emit-json \
        --builtin-directory "$builtin_directory"
  else
    timeout --kill-after=30s "${timeout_seconds}s" \
      "$krust" kcompile "$source_path" \
        --main-module WASM-TEST \
        --backend llvm \
        --output-directory "$output_directory" \
        --emit-json \
        --builtin-directory "$builtin_directory"
  fi
) >"$stdout" 2>"$stderr"
exit_code=$?
set -e
ended=$EPOCHREALTIME
wall_seconds=$(awk -v started="$started" -v ended="$ended" \
  'BEGIN { printf "%.3f", ended - started }')

timed_out=false
if ((exit_code == 124)); then
  timed_out=true
fi
if ((exit_code == 0)); then
  stage=success
  stage_rank=5
  depth=0
fi

peak_rss_kib=-1
peak_rss_measured=false
if [[ -f "$metrics" ]]; then
  measured=$(sed -n 's/^peak_rss_kib=//p' "$metrics")
  if [[ "$measured" =~ ^[0-9]+$ ]]; then
    peak_rss_kib=$measured
    peak_rss_measured=true
  fi
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
fi

regression=false
if ((stage_rank < previous_stage_rank)) || \
  ((stage_rank == previous_stage_rank && depth < previous_depth)); then
  regression=true
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
  printf 'stderr_sha256 = "%s"\n' "$stderr_sha256"
  printf 'stderr_tail = %s\n' "$stderr_tail_json"
} >"$entry"

if [[ -e "$log" ]]; then
  sed -n '/^\[\[run\]\]$/,$p' "$entry" >>"$log"
else
  cp "$entry" "$log"
fi

printf 'WASM ratchet: stage=%s depth=%s exit=%s wall=%ss rss=%sKiB log=%s\n' \
  "$stage" "$depth" "$exit_code" "$wall_seconds" "$peak_rss_kib" "$log"

if [[ "$regression" == true ]]; then
  echo "error: ratchet regression from stage rank $previous_stage_rank depth $previous_depth to stage rank $stage_rank depth $depth" >&2
  exit 3
fi
if [[ "$timed_out" == true ]]; then
  echo "error: WASM probe timed out after ${timeout_seconds}s" >&2
  exit 124
fi
