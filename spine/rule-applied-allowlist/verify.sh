#!/usr/bin/env bash
set -euo pipefail

readonly DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly REPO_ROOT="$(cd "${DIR}/../.." && pwd)"

python3 "${DIR}/verify.py" "${REPO_ROOT}"
printf 'R3-G-05 atomic rule-applied allowlist zero-backend verification: pass\n'
