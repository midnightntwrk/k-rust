#!/usr/bin/env bash
set -euo pipefail
readonly DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[[ -f "${DIR}/../../evidence/r2-g-06-k-configuration-augmentation/results.json" ]]
R2_G_06_FULL_CYCLE_COUNT=2 "${DIR}/replay.sh" "${DIR}/build/acceptance"
