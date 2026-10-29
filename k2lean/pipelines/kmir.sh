#!/usr/bin/env bash
# KMIR through k2lean, in the arity-indexed term universe: a human-run pipeline, not a gate tier.
# Each step is heavy (minutes, several GB); run it under a memory cap, one step at a time, from
# the root of a k-rust checkout:
#
#   k2lean/pipelines/kmir.sh compile        krust kcompile of KMIR (kmir.md, main module KMIR) into
#                                           $OUT/kore, for the target TARGET selects
#   k2lean/pipelines/kmir.sh survey         k2lean survey: the constructs the generator does not support
#   k2lean/pipelines/kmir.sh terms          k2lean terms --arity-terms into $OUT/terms, then lake build of it
#   k2lean/pipelines/kmir.sh gen            k2lean gen --arity-terms (with $OUT/open-obligations.txt and,
#                                           when it exists, kmir-termination.toml) into $OUT/lib, with
#                                           lean -j $LEAN_J for every module Lake builds
#   k2lean/pipelines/kmir.sh build [T...]   lake build of each target in turn (default: Terms, Functions,
#                                           Rules, Adequacy's parts, Adequacy), with the wall and CPU time, peak memory
#                                           and load of each in $OUT/logs/times.tsv and its log in
#                                           $OUT/logs/build-T.log
#   k2lean/pipelines/kmir.sh det            the determinism modules one at a time, as `build` does, then
#                                           the axiom guard of determinism alone, KMirTest.DetAxioms
#   k2lean/pipelines/kmir.sh equations      the Equations modules one at a time (its parts, then
#                                           KMir.Equations when every part built), as `build` does
#   k2lean/pipelines/kmir.sh check          lean of kmir-diverges.lean against the generated library:
#                                           the least fixed points of kmir-termination.toml have
#                                           no value where K's rewriting diverges
#   k2lean/pipelines/kmir.sh open           k2lean open-from-log of the last Equations build logs into
#                                           $OUT/open-obligations.txt, which the gen step reads
#
# TARGET selects KMIR's target by its Markdown selector:
#   concrete (default, `k & ! symbolic`): the program is the initial configuration, and its type,
#     function and allocation tables are maps in configuration cells, so one library serves every
#     program, and no rule reaches the three equation-less `lookup*Kore` functions;
#   symbolic (`k & ! concrete`): the tables are the functions `lookupTyKore`, `lookupFunctionKore`
#     and `lookupAllocKore`, whose equations are added per program, so the library has them as
#     parameters of `class Hooks`; kept generating (`gen`) so that it does not rot.
#
# This pipeline never runs KMIR programs (no `krust krun` on mir-semantics).
#
# Environment (paths may be relative to the checkout root):
#   KRUST, K2LEAN    the binaries (default target/release/krust, target/release/k2lean)
#   MIR_SOURCES      KMIR's K sources (default mir-semantics/kmir/src/kmir/kdist)
#   K_BUILTIN        K's builtin modules (default k/result/include/kframework/builtin)
#   TARGET           concrete (default) or symbolic
#   OUT              the work directory (default target/k2lean-kmir, target/k2lean-kmir-symbolic
#                    with TARGET=symbolic)
#   LEAN_J           Lean threads per module (default 8); CAP seconds per target (default 3600)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
KRUST=${KRUST:-$root/target/release/krust}
K2LEAN=${K2LEAN:-$root/target/release/k2lean}
MIR_SOURCES=${MIR_SOURCES:-$root/mir-semantics/kmir/src/kmir/kdist}
K_BUILTIN=${K_BUILTIN:-$root/k/result/include/kframework/builtin}
TARGET=${TARGET:-concrete}
case $TARGET in
  concrete) SELECTOR='k & ! symbolic'; OUT=${OUT:-$root/target/k2lean-kmir} ;;
  symbolic) SELECTOR='k & ! concrete'; OUT=${OUT:-$root/target/k2lean-kmir-symbolic} ;;
  *) echo "kmir.sh: TARGET is concrete or symbolic" >&2; exit 2 ;;
esac
LEAN_J=${LEAN_J:-8} CAP=${CAP:-3600}
RT=$root/k2lean/tests/rtime.py
lib=$OUT/lib logs=$OUT/logs
mkdir -p "$OUT" "$logs"

step=${1:-}
[ -n "$step" ] && shift
case $step in
  compile)
    [ -f "$MIR_SOURCES/mir-semantics/kmir.md" ] || { echo "kmir.sh: no KMIR sources at $MIR_SOURCES (set MIR_SOURCES)" >&2; exit 2; }
    "$RT" "$KRUST" kcompile "$MIR_SOURCES/mir-semantics/kmir.md" --main-module KMIR --syntax-module KMIR-AST \
      --md-selector "$SELECTOR" --output-directory "$OUT/kore" --builtin-directory "$K_BUILTIN" \
      -I "$MIR_SOURCES" > "$logs/compile.log" 2>&1 < /dev/null
    tail -n 1 "$logs/compile.log"
    ;;
  survey)
    "$K2LEAN" survey --kore "$OUT/kore/definition.kore" > "$OUT/survey.toml"
    echo "kmir.sh: $OUT/survey.toml"
    ;;
  terms)
    "$K2LEAN" terms --kore "$OUT/kore/definition.kore" --out "$OUT/terms" --name KMir \
      --prelude "$root/k2lean/lean" --arity-terms > "$logs/terms-gen.log" 2>&1
    sed -i 's/^  leanOptions := #\[⟨`autoImplicit, false⟩\]$/&\n  moreLeanArgs := #["-j", "'"$LEAN_J"'"]/' "$OUT/terms/lakefile.lean"
    (cd "$OUT/terms" && timeout "$CAP" "$RT" lake build) > "$logs/terms-build.log" 2>&1 || true
    grep -E 'error|rtime' "$logs/terms-build.log" | tail -n 5
    ;;
  gen)
    [ -f "$OUT/kore/definition.kore" ] || { echo "kmir.sh: run the compile step first" >&2; exit 2; }
    touch "$OUT/open-obligations.txt"
    term=()
    [ -f "$here/kmir-termination.toml" ] && term=(--termination "$here/kmir-termination.toml")
    # the determinism lemmas' heartbeat bound: RT-DATA.thunk's (a variable `EV:Evaluation`, split
    # by its leaf until the key reduces, the second search of k2l_key_cases) needs between 468,000
    # and 868,000 (2026-10-25), above the default 400,000 plus its inversions
    "$RT" "$K2LEAN" gen --kore "$OUT/kore/definition.kore" --runtime "$OUT/kore/runtime.json" --out "$lib" \
      --name KMir --prelude "$root/k2lean/lean" --arity-terms --det2-heartbeats 800000 "${term[@]}" \
      --open-obligations "$OUT/open-obligations.txt" > "$logs/gen.log" 2>&1 || { tail -n 5 "$logs/gen.log" >&2; exit 1; }
    sed -i 's/^  leanOptions := #\[⟨`autoImplicit, false⟩\]$/&\n  moreLeanArgs := #["-j", "'"$LEAN_J"'"]/' "$lib/lakefile.lean"
    grep -q moreLeanArgs "$lib/lakefile.lean"
    grep -E '^(generated|determinism:)' "$logs/gen.log" || tail -n 3 "$logs/gen.log"
    ;;
  build|equations)
    [ -f "$lib/lakefile.lean" ] || { echo "kmir.sh: run the gen step first" >&2; exit 2; }
    targets=("$@")
    if [ ${#targets[@]} = 0 ] && [ "$step" = build ]; then
      targets=(KMir.Terms KMir.Functions KMir.Rules)
      # the parts of Adequacy one at a time (Lake would build them in parallel), then Adequacy
      n=$(find "$lib/KMir/Adequacy" -name 'Part*.lean' 2> /dev/null | wc -l)
      for i in $(seq "$n"); do targets+=("KMir.Adequacy.Part$i"); done
      targets+=(KMir.Adequacy)
    elif [ ${#targets[@]} = 0 ]; then
      n=$(find "$lib/KMir/Equations" -name 'Part*.lean' 2> /dev/null | wc -l)
      for i in $(seq "$n"); do targets+=("KMir.Equations.Part$i"); done
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
    if [ "$step" = equations ] && [ $# = 0 ] && [ "$failed" = 0 ] && [ -d "$lib/KMir/Equations" ]; then
      "$0" build KMir.Equations
    fi
    ;;
  check)
    [ -f "$lib/lakefile.lean" ] || { echo "kmir.sh: run the gen step first" >&2; exit 2; }
    (cd "$lib" && "$RT" lake env lean "$here/kmir-diverges.lean") > "$logs/check.log" 2>&1 || { tail -n 20 "$logs/check.log" >&2; exit 1; }
    tail -n 7 "$logs/check.log"
    ;;
  open)
    for f in "$logs"/build-KMir.Equations*.log; do
      [ -f "$f" ] && "$K2LEAN" open-from-log "$lib/KMir/Equations.lean" "$f" "$OUT/open-obligations.txt"
    done
    ;;
  det)
    [ -f "$lib/KMir/Determinism.lean" ] || { echo "kmir.sh: run the gen step first" >&2; exit 2; }
    mods=()
    if [ -d "$lib/KMir/Determinism" ]; then
      [ -f "$lib/KMir/Determinism/Pre.lean" ] && mods+=(KMir.Determinism.Pre)
      for f in $(cd "$lib/KMir/Determinism" && ls D*.lean L*.lean 2> /dev/null | sort -V); do
        mods+=("KMir.Determinism.${f%.lean}")
      done
      [ -f "$lib/KMir/Determinism/Witness.lean" ] && mods+=(KMir.Determinism.Witness)
    fi
    mods+=(KMir.Determinism KMirTest.DetAxioms)
    "$0" build "${mods[@]}"
    ;;
  *) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 2 ;;
esac
