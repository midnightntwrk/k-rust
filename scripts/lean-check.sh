#!/usr/bin/env bash
set -euo pipefail

# Check the Lean proofs under lean/: build the KRust library, then audit its declarations for
# `sorry` and for axioms outside Lean's standard three. With --bridge, also run the proved
# definitions against the Rust they model (the k-rust-backend lean_bridge tests).

workspace=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
lean_dir="$workspace/lean"

LAKE=${LAKE:-lake}
CARGO=${CARGO:-cargo}

usage() {
  cat <<'EOF'
Usage: scripts/lean-check.sh [--bridge]

Check the Lean project in lean/:
  0. every module file under lean/KRust/ is imported by lean/KRust.lean, and neither
     lean/KRust.lean nor a module under lean/KRust/ imports the bridge library KRustBridge;
  1. `lake build` the KRust library (every module that lean/KRust.lean imports) and the
     krust-bridge executable (library KRustBridge, which evaluates the KRust definitions);
  2. `lake exe krust-audit` (lean/Audit.lean), which imports the built library, enumerates every
     declaration of the KRust modules from the Lean environment, and fails when a declaration
     depends on `sorryAx`, when a module declares an `axiom`, or when a theorem depends on an
     axiom other than propext, Classical.choice and Quot.sound.
  3. with --bridge only: `cargo test -p k-rust-backend --lib tests::lean_bridge` with
     K_RUST_LEAN_BRIDGE=1, which runs each bridged model of lean/KRust against the Rust function
     it models on generated cases (K_RUST_LEAN_BRIDGE_CASES sets the count, default 4096).

The toolchain is the one lean/lean-toolchain names, selected by elan's `lake` (LAKE overrides the
executable; CARGO overrides cargo, and CARGO_TARGET_DIR is honoured).

Exit status: 0 when every check passes, 1 when one fails, 2 on a usage error or a missing lake.
EOF
}

bridge=0
case "${1:-}" in
  -h | --help)
    usage
    exit 0
    ;;
  --bridge)
    bridge=1
    shift
    ;;
  "") ;;
  *)
    usage >&2
    exit 2
    ;;
esac
if [[ $# -gt 0 ]]; then
  usage >&2
  exit 2
fi

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
# The proofs must not depend on the harness.
while IFS= read -r file; do
  echo "lean-check: lean/$file imports KRustBridge" >&2
  missing=1
done < <(grep -rlE '^import KRustBridge' KRust.lean KRust | sort)
if [[ $missing -ne 0 ]]; then
  exit 1
fi
if ! "$LAKE" build KRust krust-audit krust-bridge; then
  echo "lean-check: lake build failed" >&2
  exit 1
fi
if ! "$LAKE" exe krust-audit; then
  echo "lean-check: the axiom audit failed" >&2
  exit 1
fi
if [[ $bridge -eq 1 ]]; then
  if ! (cd "$workspace" && K_RUST_LEAN_BRIDGE=1 LAKE="$LAKE" \
    "$CARGO" test -p k-rust-backend --lib --locked tests::lean_bridge); then
    echo "lean-check: the model conformance bridge failed" >&2
    exit 1
  fi
fi
echo "lean-check: ok"
