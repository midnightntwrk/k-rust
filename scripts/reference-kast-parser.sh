#!/usr/bin/env bash
set -euo pipefail

exec "${K_KAST:?set K_KAST to the pinned kast executable}" \
  --definition "${KAST_DEFINITION:?set KAST_DEFINITION}" \
  --sort "${KAST_PROGRAM_SORT:?set KAST_PROGRAM_SORT}" \
  --output kore \
  "$@"
