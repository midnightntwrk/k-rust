#!/usr/bin/env bash
# Runs the Python unit tests of the scripts: `python3 -m unittest discover` in every directory
# under scripts/ that holds a test_*.py module, with that directory as the import root, since the
# helpers import their siblings as top-level modules. A new test directory is found without being
# listed here.
set -euo pipefail

scripts=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
status=0
found=0
while IFS= read -r directory; do
  found=1
  echo "[script-unit-tests] scripts${directory#"$scripts"}"
  python3 -m unittest discover -s "$directory" -t "$directory" -p 'test_*.py' || status=1
done < <(find "$scripts" -name 'test_*.py' -not -path '*/__pycache__/*' -printf '%h\n' | sort -u)
((found)) || { echo "error: no test_*.py under $scripts" >&2; exit 2; }
exit "$status"
