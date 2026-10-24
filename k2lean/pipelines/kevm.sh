#!/usr/bin/env bash
# KEVM through k2lean, in the arity-indexed term universe: a human-run pipeline, not a gate tier.
# Each step is heavy (minutes, several GB); run it under a memory cap, one step at a time, from
# the root of a k-rust checkout:
#
#   k2lean/pipelines/kevm.sh compile        krust kcompile of KEVM's driver.md into $OUT/kore
#   k2lean/pipelines/kevm.sh gen            k2lean gen --arity-terms --termination kevm-termination.toml
#                                           into $OUT/lib; Rules.lean split into $RULE_MODULES matcher
#                                           modules (split-rules.py); lean -j $LEAN_J for every module
#                                           Lake builds; Adequacy bounded to $ADQ_HB heartbeats per
#                                           declaration (a runaway lemma fails instead of running on)
#   k2lean/pipelines/kevm.sh build [T...]   lake build of each target in turn (default: Terms, Functions,
#                                           RulesRel, the matcher modules, Rules, Adequacy), with the
#                                           wall and CPU time, peak memory and load of each in
#                                           $OUT/logs/times.tsv and its log in $OUT/logs/build-T.log
#   k2lean/pipelines/kevm.sh equations [P...] lake build of each module of Equations in turn (default:
#                                           every part, KEvm/Equations/Part*.lean, in order), timed
#                                           in times.tsv as `build` does, then of KEvm.Equations
#                                           (which imports the parts) when every part built; the
#                                           parts are bounded (`gen --equations-part-weight
#                                           $EQ_WEIGHT`) so that each Lean process stays under the
#                                           memory cap, and they are built one at a time because
#                                           Lake builds independent modules in parallel
#   k2lean/pipelines/kevm.sh open           k2lean open-from-log of the last Equations build logs into
#                                           $OUT/open-obligations.txt, which the gen step reads: the
#                                           failed proofs become open obligations at the next gen
#   k2lean/pipelines/kevm.sh check          kevm-sender-diverges.lean against the built Functions
#
# Determinism (`KEvm.Determinism`, along the rule index, modulo KEVM's overlapping pairs) is a
# target too, but does not build as one module under 20 GB yet (k2lean/docs/design.md, "Open").
#
# Environment (paths may be relative to the checkout root):
#   KRUST, K2LEAN    the binaries (default target/release/krust, target/release/k2lean)
#   KEVM_SOURCES     KEVM's K sources, the directory holding evm-semantics/ and plugin/ (default
#                    $EVM_SEMANTICS_CHECKOUT/kevm-pyk/src/kevm_pyk/kproj, the kevm pin of
#                    scripts/reference-differential.toml)
#   K_BUILTIN        K's builtin modules (default k/result/include/kframework/builtin)
#   OUT              the work directory (default target/k2lean-kevm)
#   LEAN_J           Lean threads per module (default 8); CAP seconds per target (default 3600);
#   ADQ_HB           Adequacy's heartbeat bound per declaration (default 2000000);
#   RULE_MODULES     matcher modules (default 4); EQ_WEIGHT the bound on one Equations module's
#                    weight (default: the generator's)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
KRUST=${KRUST:-$root/target/release/krust}
K2LEAN=${K2LEAN:-$root/target/release/k2lean}
KEVM_SOURCES=${KEVM_SOURCES:-${EVM_SEMANTICS_CHECKOUT:-$root/evm-semantics}/kevm-pyk/src/kevm_pyk/kproj}
K_BUILTIN=${K_BUILTIN:-$root/k/result/include/kframework/builtin}
OUT=${OUT:-$root/target/k2lean-kevm}
LEAN_J=${LEAN_J:-8} CAP=${CAP:-3600} ADQ_HB=${ADQ_HB:-2000000} RULE_MODULES=${RULE_MODULES:-4} EQ_WEIGHT=${EQ_WEIGHT:-}
RT=$root/k2lean/tests/rtime.py
lib=$OUT/lib logs=$OUT/logs
mkdir -p "$OUT" "$logs"

step=${1:-}
[ -n "$step" ] && shift
case $step in
  compile)
    [ -x "$KRUST" ] || { echo "kevm.sh: needs krust at $KRUST" >&2; exit 2; }
    [ -f "$KEVM_SOURCES/evm-semantics/driver.md" ] || { echo "kevm.sh: no KEVM sources at $KEVM_SOURCES (set KEVM_SOURCES)" >&2; exit 2; }
    "$RT" "$KRUST" kcompile "$KEVM_SOURCES/evm-semantics/driver.md" --main-module ETHEREUM-SIMULATION \
      --syntax-module ETHEREUM-SIMULATION --output-directory "$OUT/kore" --builtin-directory "$K_BUILTIN" \
      -I "$KEVM_SOURCES/evm-semantics" -I "$KEVM_SOURCES/plugin" > "$logs/compile.log" 2>&1
    tail -n 1 "$logs/compile.log"
    ;;
  gen)
    [ -f "$OUT/kore/definition.kore" ] || { echo "kevm.sh: run the compile step first" >&2; exit 2; }
    touch "$OUT/open-obligations.txt"
    "$RT" "$K2LEAN" gen --kore "$OUT/kore/definition.kore" --runtime "$OUT/kore/runtime.json" --out "$lib" \
      --name KEvm --prelude "$root/k2lean/lean/prelude" --arity-terms --termination "$here/kevm-termination.toml" \
      --open-obligations "$OUT/open-obligations.txt" ${EQ_WEIGHT:+--equations-part-weight "$EQ_WEIGHT"} \
      > "$logs/gen.log" 2>&1
    python3 -I "$here/split-rules.py" "$lib" KEvm "$RULE_MODULES"
    sed -i 's/^  leanOptions := #\[⟨`autoImplicit, false⟩\]$/&\n  moreLeanArgs := #["-j", "'"$LEAN_J"'"]/' "$lib/lakefile.lean"
    grep -q moreLeanArgs "$lib/lakefile.lean"
    sed -i "s/^set_option maxHeartbeats 0$/set_option maxHeartbeats $ADQ_HB/" "$lib/KEvm/Adequacy.lean"
    grep -E '^(generated|determinism:)' "$logs/gen.log" || true
    ;;
  build|equations)
    [ -f "$lib/lakefile.lean" ] || { echo "kevm.sh: run the gen step first" >&2; exit 2; }
    targets=("$@")
    if [ ${#targets[@]} = 0 ] && [ "$step" = build ]; then
      targets=(KEvm.Terms KEvm.Functions KEvm.RulesRel)
      for i in $(seq "$RULE_MODULES"); do targets+=("KEvm.RulesM$i"); done
      targets+=(KEvm.Rules KEvm.Adequacy)
    elif [ ${#targets[@]} = 0 ]; then
      n=$(find "$lib/KEvm/Equations" -name 'Part*.lean' 2> /dev/null | wc -l)
      for i in $(seq "$n"); do targets+=("KEvm.Equations.Part$i"); done
    fi
    [ -f "$logs/times.tsv" ] || printf 'target\twall_s\tcpu_s\tpeak_mib\texit\tload_start\tload_end\terrors\n' > "$logs/times.tsv"
    failed=0
    for t in "${targets[@]}"; do
      l0=$(cut -d' ' -f1 /proc/loadavg)
      (cd "$lib" && timeout "$CAP" "$RT" lake build "$t") > "$logs/build-$t.log" 2>&1 || true
      r=$(grep -o 'rtime: .*' "$logs/build-$t.log" | tail -n 1)
      wall=$(sed -n 's/.*wall \([0-9.]*\) s.*/\1/p' <<< "$r") cpu=$(sed -n 's/.*cpu \([0-9.]*\) s.*/\1/p' <<< "$r")
      rss=$(sed -n 's/.*rss \([0-9]*\) MiB.*/\1/p' <<< "$r") rc=$(sed -n 's/.*exit \([0-9-]*\).*/\1/p' <<< "$r")
      [ "${rc:-1}" = 0 ] || failed=1
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$t" "${wall:-}" "${cpu:-}" "${rss:-}" "${rc:-timeout}" "$l0" \
        "$(cut -d' ' -f1 /proc/loadavg)" "$(grep -c 'error:' "$logs/build-$t.log" || true)" >> "$logs/times.tsv"
      tail -n 1 "$logs/times.tsv"
    done
    # the module that imports the parts, once they are built (with a part failing, Lake would
    # build the failing parts again, all at once)
    if [ "$step" = equations ] && [ $# = 0 ] && [ "$failed" = 0 ]; then
      "$0" build KEvm.Equations
    fi
    ;;
  open)
    for f in "$logs"/build-KEvm.Equations*.log; do
      [ -f "$f" ] && "$K2LEAN" open-from-log "$lib/KEvm/Equations.lean" "$f" "$OUT/open-obligations.txt"
    done
    ;;
  check)
    (cd "$lib" && "$RT" lake env lean "$here/kevm-sender-diverges.lean") > "$logs/check.log" 2>&1
    tail -n 3 "$logs/check.log"
    ;;
  *) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 2 ;;
esac
