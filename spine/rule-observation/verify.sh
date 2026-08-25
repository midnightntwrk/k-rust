#!/usr/bin/env bash
set -euo pipefail
readonly DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[[ -f "${DIR}/../../evidence/r2-g-07-single-rule-observation/results.json" ]]
R2_G_07_FULL_CYCLE_COUNT=3 "${DIR}/replay.sh" "${DIR}/build/acceptance"
