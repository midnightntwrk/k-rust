#!/usr/bin/env bash
# KMIR through k2lean, in the arity-indexed term universe: a human-run pipeline, not a gate tier.
# Run from the root of a k-rust checkout, one heavy step at a time under a memory cap:
#
#   k2lean/pipelines/kmir.sh compile    krust kcompile of KMIR (kmir.md, `k & ! concrete`) into $OUT/kore
#   k2lean/pipelines/kmir.sh survey     k2lean survey: the constructs the generator does not support
#   k2lean/pipelines/kmir.sh terms      k2lean terms --arity-terms into $OUT/terms, then lake build of it
#   k2lean/pipelines/kmir.sh gen        k2lean gen --arity-terms into $OUT/lib (stops at the definition's
#                                       `ensures` rule, which the generator does not support yet)
#
# This pipeline never runs KMIR programs (no `krust krun` on mir-semantics).
#
# Environment: KRUST, K2LEAN (default target/release/krust, target/release/k2lean); MIR_SOURCES
# (default mir-semantics/kmir/src/kmir/kdist); K_BUILTIN (default k/result/include/kframework/builtin);
# OUT (default target/k2lean-kmir); LEAN_J (Lean threads, default 8); CAP (seconds, default 3600).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
KRUST=${KRUST:-$root/target/release/krust}
K2LEAN=${K2LEAN:-$root/target/release/k2lean}
MIR_SOURCES=${MIR_SOURCES:-$root/mir-semantics/kmir/src/kmir/kdist}
K_BUILTIN=${K_BUILTIN:-$root/k/result/include/kframework/builtin}
OUT=${OUT:-$root/target/k2lean-kmir}
LEAN_J=${LEAN_J:-8} CAP=${CAP:-3600}
RT=$root/k2lean/tests/rtime.py
logs=$OUT/logs
mkdir -p "$OUT" "$logs"

case ${1:-} in
  compile)
    [ -f "$MIR_SOURCES/mir-semantics/kmir.md" ] || { echo "kmir.sh: no KMIR sources at $MIR_SOURCES (set MIR_SOURCES)" >&2; exit 2; }
    "$RT" "$KRUST" kcompile "$MIR_SOURCES/mir-semantics/kmir.md" --main-module KMIR --syntax-module KMIR-AST \
      --md-selector 'k & ! concrete' --output-directory "$OUT/kore" --builtin-directory "$K_BUILTIN" \
      -I "$MIR_SOURCES" > "$logs/compile.log" 2>&1 < /dev/null
    tail -n 1 "$logs/compile.log"
    ;;
  survey)
    "$K2LEAN" survey --kore "$OUT/kore/definition.kore" > "$OUT/survey.toml"
    echo "kmir.sh: $OUT/survey.toml"
    ;;
  terms)
    "$K2LEAN" terms --kore "$OUT/kore/definition.kore" --out "$OUT/terms" --name KMir \
      --prelude "$root/k2lean/lean/prelude" --arity-terms > "$logs/terms-gen.log" 2>&1
    sed -i 's/^  leanOptions := #\[⟨`autoImplicit, false⟩\]$/&\n  moreLeanArgs := #["-j", "'"$LEAN_J"'"]/' "$OUT/terms/lakefile.lean"
    (cd "$OUT/terms" && timeout "$CAP" "$RT" lake build) > "$logs/terms-build.log" 2>&1 || true
    grep -E 'error|rtime' "$logs/terms-build.log" | tail -n 5
    ;;
  gen)
    "$RT" "$K2LEAN" gen --kore "$OUT/kore/definition.kore" --runtime "$OUT/kore/runtime.json" --out "$OUT/lib" \
      --name KMir --prelude "$root/k2lean/lean/prelude" --arity-terms > "$logs/gen.log" 2>&1 || true
    tail -n 3 "$logs/gen.log"
    ;;
  *) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 2 ;;
esac
