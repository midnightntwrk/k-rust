#!/usr/bin/env bash
set -euo pipefail
readonly DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ "${R3_G_02_FREEZE_EVIDENCE:-0}" != "1" ]]; then
  [[ -f "${DIR}/../../evidence/r3-g-02-k-authored-trace-configuration/results.json" ]]
  [[ -f "${DIR}/../../evidence/r3-g-02-k-authored-trace-configuration/report.md" ]]
fi
R3_G_02A_REPAIR_CYCLE_COUNT=2 "${DIR}/replay.sh" "${DIR}/build/acceptance"
