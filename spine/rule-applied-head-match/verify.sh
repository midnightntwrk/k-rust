#!/usr/bin/env bash
set -euo pipefail
readonly DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ "${R3_G_03_FREEZE_EVIDENCE:-0}" != "1" ]]; then
  [[ -f "${DIR}/../../evidence/r3-g-03-k-native-rule-applied-head-match/results.json" ]]
  [[ -f "${DIR}/../../evidence/r3-g-03-k-native-rule-applied-head-match/report.md" ]]
fi
"${DIR}/replay.sh" "${DIR}/build/acceptance"
