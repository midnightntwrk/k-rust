#!/usr/bin/env bash
set -euo pipefail

readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
[[ -f "${SCRIPT_DIR}/results.json" ]]
R2_G_05_FULL_CYCLE_COUNT=3 "${SCRIPT_DIR}/replay.sh" "${SCRIPT_DIR}/build/acceptance"
