#!/usr/bin/env bash
# SIMPLE against a variant of it through `k2lean relate` (demos/SimpleRel): a human-run pipeline,
# not a gate tier, because the relation's simulations cost more than a gate tier allows
# (k2lean/docs/design.md, section 9). Run it from the root of a k-rust checkout, one step at a
# time, under a memory cap:
#
#   k2lean/pipelines/simple-rel.sh compile      krust kcompile of SIMPLE and of its variant
#                                               (k2lean/tests/simple-variant.py: three constructors
#                                               under other symbols, the rules in another order)
#                                               into $OUT/kore
#   k2lean/pipelines/simple-rel.sh gen          a work tree $OUT/k2lean (copies of lean/ and
#                                               demos/SimpleRel), the libraries simple and simplev
#                                               (k2lean gen, as in the gate) and the relation
#                                               (k2lean relate: demos/SimpleRel/SimpleRel/Bisim.lean
#                                               and correspondence.toml)
#   k2lean/pipelines/simple-rel.sh build [T...] lake build of each target in turn (default:
#                                               KSimple.Rules, KSimpleV.Rules, SimpleRel), with the
#                                               wall and CPU time, peak memory and load of each in
#                                               $OUT/logs/times.tsv and its log in
#                                               $OUT/logs/build-T.log
#
# The generator calls are tests/libs.sh's, shared with the gate and demos/regen.sh.
#
# Encoding: per-sort. Both libraries and the relation are generated in the per-sort encoding
# (`gen --per-sort-terms`, `relate --per-sort-terms true`), a holdout of the arity universe that is
# otherwise the default (k2lean/docs/design.md, section 2.1): session C (k-rust-c1) is proving
# SimpleRel's simulations (REL-1) against the per-sort form, and moving SimpleRel to the arity
# universe is that session's decision.
#
# Environment (paths may be relative to the checkout root):
#   KRUST, K2LEAN    the binaries (default target/release/krust, target/release/k2lean)
#   K_BUILTIN        K's builtin modules (default k/k-distribution/include/kframework/builtin)
#   SD               SIMPLE's K sources (default the K checkout's pl-tutorial 1_simple/1_untyped)
#   OUT              the work directory (default target/k2lean-simple-rel)
#   CAP              seconds per build target (default 3600)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
KRUST=${KRUST:-$root/target/release/krust}
K2LEAN=${K2LEAN:-$root/target/release/k2lean}
BUILTIN=${K_BUILTIN:-$root/k/k-distribution/include/kframework/builtin}
SD=${SD:-$root/k/pyk/regression-new/pl-tutorial/2_languages/1_simple/1_untyped}
OUT=${OUT:-$root/target/k2lean-simple-rel}
CAP=${CAP:-3600}
RT=$root/k2lean/tests/rtime.py
mkdir -p "$OUT/logs"
OUT=$(cd "$OUT" && pwd)
logs=$OUT/logs T=$OUT/k2lean
# what tests/libs.sh reads; G adds the per-sort flags (see Encoding above) to gen and relate
k2lean_per_sort() {
  local c=$1; shift
  case $c in
    gen) "$K2LEAN" gen "$@" --per-sort-terms ;;
    relate) "$K2LEAN" relate "$@" --per-sort-terms true ;;
    *) "$K2LEAN" "$c" "$@" ;;
  esac
}
G=k2lean_per_sort GEN=$T/generated DEMOS=$T/demos
kore_dir() { echo "$OUT/kore/$1"; }
# shellcheck source=../tests/libs.sh
. "$root/k2lean/tests/libs.sh"

step=${1:-}
[ -n "$step" ] && shift
case $step in
  compile)
    [ -x "$KRUST" ] || { echo "simple-rel.sh: needs krust at $KRUST" >&2; exit 2; }
    [ -d "$SD" ] || { echo "simple-rel.sh: no SIMPLE sources at $SD (set SD)" >&2; exit 2; }
    for k in simple simple-variant; do
      libs_kcompile "$k" > "$logs/compile-$k.log" 2>&1 || { tail -n 5 "$logs/compile-$k.log"; exit 1; }
      echo "compiled $k"
    done
    ;;
  gen)
    [ -x "$K2LEAN" ] || { echo "simple-rel.sh: needs k2lean at $K2LEAN" >&2; exit 2; }
    [ -f "$OUT/kore/simple-variant/definition.kore" ] || { echo "simple-rel.sh: run the compile step first" >&2; exit 2; }
    mkdir -p "$T/lean" "$T/demos/SimpleRel" "$GEN/simple" "$GEN/simplev"
    rsync -a --delete --exclude=.lake "$root/k2lean/lean/" "$T/lean/"
    rsync -a --exclude=.lake "$root/k2lean/demos/SimpleRel/" "$T/demos/SimpleRel/"
    # the variant has SIMPLE's functions, so it starts from SIMPLE's open list
    for d in simple simplev; do cp "$root/k2lean/generated/simple/open-obligations.txt" "$GEN/$d/open-obligations.txt"; done
    for d in simple simplev; do
      libs_gen "$d" > "$logs/gen-$d.log" 2>&1 || { tail -n 5 "$logs/gen-$d.log"; exit 1; }
      echo "generated $d"
    done
    libs_relate SimpleRel > "$logs/relate.log" 2>&1 || { tail -n 5 "$logs/relate.log"; exit 1; }
    tail -n 1 "$logs/relate.log"
    ;;
  build)
    [ -f "$T/demos/SimpleRel/SimpleRel/Bisim.lean" ] || { echo "simple-rel.sh: run the gen step first" >&2; exit 2; }
    targets=("$@")
    [ ${#targets[@]} = 0 ] && targets=(KSimple.Rules KSimpleV.Rules SimpleRel)
    [ -f "$logs/times.tsv" ] || printf 'target\twall_s\tcpu_s\tpeak_mib\texit\tload_start\tload_end\terrors\n' > "$logs/times.tsv"
    for t in "${targets[@]}"; do
      case $t in KSimple.*) dir=$GEN/simple ;; KSimpleV.*) dir=$GEN/simplev ;; *) dir=$T/demos/SimpleRel ;; esac
      l0=$(cut -d' ' -f1 /proc/loadavg)
      (cd "$dir" && timeout "$CAP" "$RT" lake build "$t") > "$logs/build-$t.log" 2>&1 || true
      r=$(grep -o 'rtime: .*' "$logs/build-$t.log" | tail -n 1 || true)
      wall=$(sed -n 's/.*wall \([0-9.]*\) s.*/\1/p' <<< "$r") cpu=$(sed -n 's/.*cpu \([0-9.]*\) s.*/\1/p' <<< "$r")
      rss=$(sed -n 's/.*rss \([0-9]*\) MiB.*/\1/p' <<< "$r") rc=$(sed -n 's/.*exit \([0-9-]*\).*/\1/p' <<< "$r")
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$t" "${wall:-}" "${cpu:-}" "${rss:-}" "${rc:-timeout}" "$l0" \
        "$(cut -d' ' -f1 /proc/loadavg)" "$(grep -c 'error:' "$logs/build-$t.log" || true)" >> "$logs/times.tsv"
      tail -n 1 "$logs/times.tsv"
    done
    ;;
  *) sed -n '2,/^set -euo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 2 ;;
esac
