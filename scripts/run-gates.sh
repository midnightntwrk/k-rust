#!/usr/bin/env bash
# Runs entries of the gate registry, scripts/gates.toml (scripts/run_gates.py; --help for usage).
set -euo pipefail
exec python3 "$(dirname "${BASH_SOURCE[0]}")/run_gates.py" "$@"
