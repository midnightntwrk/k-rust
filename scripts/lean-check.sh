#!/usr/bin/env bash
set -euo pipefail

# Check the Lean proofs under lean/: build the KRust library, then audit its declarations for
# `sorry` and for axioms outside Lean's standard three.

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$workspace/lean"

LAKE=${LAKE:-lake}

usage() {
  cat <<'EOF'
Usage: scripts/lean-check.sh

Check the Lean project in lean/:
  0. every module file under lean/KRust/ is imported by lean/KRust.lean;
  1. `lake build` the KRust library (every module that lean/KRust.lean imports);
  2. `lake exe krust-audit` (lean/Audit.lean), which imports the built library, enumerates every
     declaration of the KRust modules from the Lean environment, and fails when a declaration
     depends on `sorryAx`, when a module declares an `axiom`, or when a theorem depends on an
     axiom other than propext, Classical.choice and Quot.sound.

The toolchain is the one lean/lean-toolchain names, selected by elan's `lake` (LAKE overrides the
executable).

Exit status: 0 when the build and the audit pass, 1 when either fails, 2 when lake is missing.
EOF
}

case "${1:-}" in
  -h | --help)
    usage
    exit 0
    ;;
  "") ;;
  *)
    usage >&2
    exit 2
    ;;
esac

if ! command -v "$LAKE" >/dev/null 2>&1; then
  echo "error: $LAKE is not on PATH; install elan, which selects the toolchain in lean/lean-toolchain" >&2
  exit 2
fi
if ! (cd "$lean_dir" && "$LAKE" --version >/dev/null); then
  echo "error: $LAKE cannot start the toolchain named by $lean_dir/lean-toolchain" >&2
  exit 2
fi

cd "$lean_dir"
# The audit sees only what lean/KRust.lean imports, so every module file must be imported there.
missing=0
while IFS= read -r file; do
  module=${file%.lean}
  module=${module//\//.}
  if ! grep -qxF "import $module" KRust.lean; then
    echo "lean-check: lean/KRust.lean does not import $module" >&2
    missing=1
  fi
done < <(find KRust -name '*.lean' | sort)
if [[ $missing -ne 0 ]]; then
  exit 1
fi
if ! "$LAKE" build KRust krust-audit; then
  echo "lean-check: lake build failed" >&2
  exit 1
fi
if ! "$LAKE" exe krust-audit; then
  echo "lean-check: the axiom audit failed" >&2
  exit 1
fi
echo "lean-check: ok"
