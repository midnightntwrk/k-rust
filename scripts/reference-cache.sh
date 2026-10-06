#!/usr/bin/env bash
# The reference-output cache of the differential gates (scripts/reference_cache.py has the key,
# entry and mode contract). Source this file after reference-pins.sh and call
# reference_cache_begin after the gate's pin checks; a case-specific pin check must precede that
# case's first reference call. The cache keys on the pins, so a lookup never stands in for a pin
# check. Without kdep beside kompile, kompile and kprove results are recomputed and not stored.
#
#   REFERENCE_CACHE=off|on|refresh|verify   default on; off when CI=true or when
#                                           REFERENCE_DIFFERENTIAL_ALLOW_UNPINNED=1
#   REFERENCE_CACHE_DIR                     default ${XDG_CACHE_HOME:-~/.cache}/k-rust/reference-outputs/v1
#   REFERENCE_CACHE_MAX_AGE_DAYS            default 14; an older entry is recomputed
#   REFERENCE_CACHE_LOG                     JSON lines, one per reference call (default: in the work directory)

reference_cache_tool="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/reference_cache.py"
reference_cache_work=

# reference_cache_begin WORK
#   Validates the mode, exports the pins every key includes, and opens the run log. WORK is the
#   gate's per-run scratch directory; paths below it enter keys as a placeholder, because each
#   uncached run already uses a fresh random directory, so no verdict can depend on its name.
reference_cache_begin() {
  reference_cache_work=$1
  python3 "$reference_cache_tool" mode >/dev/null || return 2
  # shellcheck disable=SC2154  # reference-pins.sh, sourced before this file, defines it
  REFERENCE_CACHE_PINS=$(jq -c '.reference' <<<"$reference_manifest_json")
  REFERENCE_CACHE_SCRIPT=$(basename "${BASH_SOURCE[1]:-gate}")
  REFERENCE_CACHE_LOG=${REFERENCE_CACHE_LOG:-"$reference_cache_work/reference-cache.jsonl"}
  export REFERENCE_CACHE_PINS REFERENCE_CACHE_SCRIPT REFERENCE_CACHE_LOG
}

# reference_cached TOOL LABEL [CACHE OPTION...] -- COMMAND [ARGUMENT...]
#   Runs or replays one reference tool invocation in the current directory, with the caller's
#   environment, resource limits and redirections. Cache options (scripts/reference_cache.py run
#   --help): --output-root DIR for every directory the tool writes that the gate reads,
#   --input PATH for every file or directory it reads besides its argument vector's K sources,
#   --kdep KDEP to key a kompile or kprove on its requires closure, --stdin when it reads
#   standard input, --env NAME for a further variable it reads, and --store-status N to store
#   only those exit statuses.
reference_cached() {
  local tool=$1
  local label=$2
  shift 2
  python3 "$reference_cache_tool" run --tool "$tool" --label "$label" \
    --placeholder "work=$reference_cache_work" "$@"
}

# reference_cache_finish
#   Prints the per-run hit and miss counts (the step records of every call are in
#   REFERENCE_CACHE_LOG) and fails when verify mode found an entry that a fresh run contradicts.
reference_cache_finish() {
  python3 "$reference_cache_tool" summary --log "$REFERENCE_CACHE_LOG"
}
