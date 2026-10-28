#!/usr/bin/env bash
# k2lean's regression gate.
# Regenerates every library and demonstration from the K sources with the generator under test,
# builds them in a scratch work tree, and compares what it measures with the baseline
# (tests/baseline/AREA.toml, with the recorded outputs in tests/expected/AREA/).
#
#   k2lean/tests/gate.sh light    the generator's unit and snapshot tests, then every entry of tier light
#   k2lean/tests/gate.sh heavy    light, then every entry of tier heavy (SIMPLE and what is built on
#                                 it, and the claims)
#   k2lean/tests/gate.sh list [TIER]
#                                 print the registered entries by area: kind, name, tier, the tiers
#                                 that only compare it, and its term encoding (arity or per-sort;
#                                 all entries, or those a TIER run measures)
#   k2lean/tests/gate.sh accept [--area NAME]
#                                 make the last run's measurements the baseline, of every area, or of
#                                 area NAME only, which is refused (naming the entries) when another
#                                 area's measured entries differ from that area's baseline, unless the
#                                 run measured that area as the baseline it started from records it
#                                 (the baseline moved since), or when NAME's own baseline moved; entries
#                                 of the tiers the run did not include are kept, and a recorded output
#                                 is rewritten only when its normalized content changes
#
# Each entry is registered in one area, in tests/areas/AREA.sh (its generator calls and gate
# phases, see tests/libs.sh) and tests/areas/AREA.py (what is measured, each entry with its tier);
# `list` prints them, and docs/testing.md of the repository says what each area owns. The areas
# run in the order of LIBS_AREAS (tests/libs.sh), each running the entries of its own that the
# tier includes.
#
# Exit status: 0 the tier passes; 1 a regression (the `FAIL` lines say which); 2 a setup error.
# A clean light run builds eleven Lean libraries and six Lean projects: on 2026-10-24, on Lean
# v4.34.0 and a shared 32-CPU host, it took 1,103 s wall, 1,552 s of CPU and 4.1 GB of peak memory
# under a load of 28 to 31; a clean heavy run took 2,709 s wall, 3,343 s of CPU and 8.5 GB under a
# load of 26 to 56 (both before the switch to the arity universe; the former arity tier took 442 s,
# 860 s and 4.2 GB under a load of 31 to 48). A rerun
# rebuilds only what changed (26 s light, 50 s heavy, measured on Lean v4.30.0 with fewer libraries).
#
# Needs: krust (a release build), the K release's `kompile` with its LLVM backend (kimp's step
# traces), the K sources and kimp's sources at the pins of scripts/reference-differential.toml
# (README.md, "Compatibility evidence"), cargo, lake (elan), z3 (the rule-pair classification and
# the overlap witnesses of `gen`) and python3 >= 3.11 on PATH.
#
# Environment (paths may be relative to the current directory):
#   GATE_ROOT=DIR       the k2lean directory under test (default: the one holding this script); it
#                       needs lean/, demos/ and generated/ (the open-obligation lists), and its
#                       parent must be the k-rust workspace the generator is built in, so a
#                       worktree or a copy of the whole checkout can be tested; its tests/libs.sh
#                       and tests/areas/ are used when it has them, else this script's
#   GATE_KRUST_REPO=DIR the k-rust checkout whose krust, K sources and kimp sources the gate uses
#                       (default: the checkout holding this script)
#   GATE_KRUST=FILE     krust (default GATE_KRUST_REPO/target/release/krust)
#   K_KOMPILE=FILE      K's kompile (default GATE_KRUST_REPO/k/result/bin/kompile when present,
#                       else `kompile` on PATH)
#   GATE_K_CHECKOUT=DIR the K sources (default GATE_KRUST_REPO/k): the builtin modules
#                       (k-distribution/include/kframework/builtin, or GATE_K_BUILTIN=DIR) and, for
#                       heavy, SIMPLE (pyk/regression-new/pl-tutorial)
#   GATE_IMP_CHECKOUT=DIR imp-semantics (default GATE_KRUST_REPO/imp-semantics): kimp and, for heavy,
#                       its claims (examples/specs)
#   GATE_KIMP=DIR       kimp's K sources (default GATE_IMP_CHECKOUT/src/kimp/kdist/imp-semantics)
#   GATE_WORK=DIR       the work tree (default target/k2lean-gate/work/<name of the root> in the
#                       checkout holding this script): a copy of the tree under test whose .lake/
#                       directories and Cargo target are kept between runs, so a rerun builds only
#                       what changed
#   GATE_SEED=DIR       when the work tree has no .lake/ yet, copy those of another work tree first
#                       (the .lake/ directories only, not its Cargo target)
#   GATE_CLEAN=1        delete the work tree's .lake/ directories and Cargo target first
#   GATE_RETRY_OPEN=1   start every library from an open-obligation list holding only the entries
#                       marked refuted, so every other open obligation is attempted again (finds
#                       removals; rebuilds every Equations)
#   GATE_BASELINE=DIR   the baseline (default tests/baseline next to this script): one AREA.toml per
#                       area; the recorded outputs are in expected/AREA/ beside it
#   GATE_CACHE=DIR      outputs cached by the hash of their inputs (default target/k2lean-gate/cache
#                       in the checkout holding this script): kimp's K LLVM interpreter, SIMPLE's
#                       krust-derived cases; GATE_CLEAN keeps it. Concurrent runs may share it: each
#                       entry is written under a temporary name and renamed into place
#
# The gate starts each library from the open-obligation list of the tree under test, so it finds
# a proof that stopped working (a new open member) but not one that started working; that needs
# GATE_RETRY_OPEN=1. A failed equation proof is found by building `Equations`, turning the
# failures into open obligations and rebuilding, at most three times; a proof that ends in a
# heartbeat timeout costs minutes per attempt.
set -uo pipefail

TIER=${1:-}
SELF=$(cd "$(dirname "$0")/.." && pwd)   # the k2lean directory holding this script
REPO=$(dirname "$SELF")                  # the k-rust checkout holding it
CHECK=$SELF/tests/gate-check.py
RT=$SELF/tests/rtime.py
BASE=${GATE_BASELINE:-$SELF/tests/baseline}
ROOT=$(cd "${GATE_ROOT:-$SELF}" && pwd)
# the registrations (tests/libs.sh and tests/areas/): the tree under test's, else this one's
TESTS=$ROOT/tests; [ -f "$TESTS/libs.sh" ] && [ -d "$TESTS/areas" ] || TESTS=$SELF/tests
export GATE_AREAS=$TESTS/areas
if [ "$ROOT" = "$SELF" ]; then name=main; else name=$(basename "$(dirname "$ROOT")")-$(printf %s "$ROOT" | sha256sum | cut -c1-8); fi
W=${GATE_WORK:-$REPO/target/k2lean-gate/work/$name}
CACHE=${GATE_CACHE:-$REPO/target/k2lean-gate/cache}

case $TIER in
  light|heavy) ;;
  list) shift; exec python3 -I "$CHECK" list "$@" ;;
  accept) shift; exec python3 -I "$CHECK" accept "$W" "$BASE" "$@" ;;
  *) sed -n '2,/^set -uo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 2 ;;
esac
mkdir -p "$W" "$CACHE"
W=$(cd "$W" && pwd) CACHE=$(cd "$CACHE" && pwd)

need() { echo "gate: needs $*" >&2; exit 2; }
R=$(cd "${GATE_KRUST_REPO:-$REPO}" && pwd)
KRUST=${GATE_KRUST:-$R/target/release/krust}
KOMPILE=${K_KOMPILE:-}
if [ -z "$KOMPILE" ]; then
  if [ -x "$R/k/result/bin/kompile" ]; then KOMPILE=$R/k/result/bin/kompile; else KOMPILE=$(command -v kompile || true); fi
fi
KCHECKOUT=${GATE_K_CHECKOUT:-$R/k}
BUILTIN=${GATE_K_BUILTIN:-$KCHECKOUT/k-distribution/include/kframework/builtin}
IMPCHECKOUT=${GATE_IMP_CHECKOUT:-$R/imp-semantics}
KIMP=${GATE_KIMP:-$IMPCHECKOUT/src/kimp/kdist/imp-semantics}
SPECS=$IMPCHECKOUT/examples/specs
SD=$KCHECKOUT/pyk/regression-new/pl-tutorial/2_languages/1_simple/1_untyped
GOLDENS=$ROOT/tests/goldens
[ -x "$KRUST" ] || need "krust at $KRUST (cargo build --release -p k-rust --bin krust, or set GATE_KRUST)"
[ -n "$KOMPILE" ] && [ -x "$KOMPILE" ] || need "K's kompile (set K_KOMPILE or put it on PATH)"
[ -d "$BUILTIN" ] || need "K's builtin modules at $BUILTIN (set GATE_K_CHECKOUT or GATE_K_BUILTIN)"
[ -d "$KIMP" ] || need "kimp's sources at $KIMP (set GATE_IMP_CHECKOUT or GATE_KIMP)"
[ -d "$GOLDENS" ] || need "the golden cases at $GOLDENS"
for t in cargo lake python3 rsync z3; do command -v "$t" > /dev/null || need "$t on PATH"; done
python3 -c 'import tomllib' 2> /dev/null || need "python3 >= 3.11 (tomllib)"
for f in "$CHECK" "$RT" "$BASE"; do [ -e "$f" ] || need "$f"; done
for d in lean demos generated; do
  [ -d "$ROOT/$d" ] || { echo "gate: $ROOT has no $d/" >&2; exit 2; }
done
[ -f "$ROOT/../Cargo.toml" ] || need "the k-rust workspace around $ROOT (its Cargo.toml)"
KIMP=$(cd "$KIMP" && pwd)
export CARGO_TARGET_DIR=$W/target

T=$W/k2lean            # the copy of the tree under test
GEN=$T/generated
D=$T/demos
KO=$W/kore             # krust's compiled definitions
L=$W/logs
MEAS=$W/measured       # what this run measured (gate-check.py reads it)
# the generator calls and the areas' phases (tests/libs.sh, shared with demos/regen.sh)
# shellcheck source=libs.sh
. "$TESTS/libs.sh"
DEMOS=$D KRS=$D/k/krs-imp FIXTURES=$ROOT/tests/fixtures
kore_dir() { echo "$KO/$1"; }

# the entries this tier runs, by kind and name (each area's registry declares an entry's tier)
declare -A RUN=()
entries=$(python3 -I "$CHECK" entries "$TIER") || need "a readable registry in $GATE_AREAS (gate-check.py entries)"
while read -r kind ename; do [ -n "$kind" ] && RUN["$kind $ename"]=1; done <<< "$entries"
runs() { [ -n "${RUN["$1 $2"]:-}" ]; }   # KIND NAME: does this tier run the entry
for a in $LIBS_AREAS; do ! declare -F "needs_$a" > /dev/null || "needs_$a"; done

rm -rf "$L" "$MEAS"
mkdir -p "$L" "$MEAS" "$KO"
STATUS=$MEAS/status.tsv
TIMES=$MEAS/times.tsv
printf 'step\tresult\tlog\n' > "$STATUS"
printf 'phase\twall_s\tcpu_s\tload_at_start\n' > "$TIMES"
printf 'tier = "%s"\nroot = "%s"\nkimp = "%s"\nstarted = "%s"\n' "$TIER" "$ROOT" "$KIMP" "$(date -Is)" > "$MEAS/run.toml"
# the baseline and registry this run starts from, so that `accept --area` can tell an area this run
# measured differently from one whose baseline moved after the run started (another session's landing)
mkdir -p "$MEAS/against/registry"
cp -a "$BASE" "$MEAS/against/baseline"
cp -a "$GATE_AREAS" "$MEAS/against/registry/areas"
cp -a "$TESTS/libs.sh" "$MEAS/against/registry/libs.sh"
[ ! -d "$(dirname "$BASE")/expected" ] || cp -a "$(dirname "$BASE")/expected" "$MEAS/against/expected"

echo "gate: $TIER, root $ROOT, kimp $KIMP"
echo "gate: work tree $W, load $(cut -d' ' -f1-3 /proc/loadavg)"

ok() { printf '%s\tok\t%s\n' "$1" "${2:-}" >> "$STATUS"; }
bad() { # STEP LOG: record a failed step and show its first errors
  printf '%s\tfail\t%s\n' "$1" "${2:-}" >> "$STATUS"
  echo "gate: FAIL step $1 (log ${2:-none})"
  [ -n "${2:-}" ] && [ -f "$2" ] && { grep -E '^error|error:|FAIL|panicked' "$2" | head -8 | sed 's/^/gate:   /'; }
  return 0
}
# CPU seconds of this shell's finished children; `times` runs in this shell (in a command
# substitution it would report the subshell's children)
cpu() { times > "$W/.times"; sed -n 2p "$W/.times" | awk '{ s = 0; for (i = 1; i <= 2; i++) { split($i, a, /[ms]/); s += a[1] * 60 + a[2] } printf "%.1f", s }'; }
P_NAME='' P_T0='' P_C0='' P_L0=''
phase() { # NAME: close the running phase, open the next one ("" closes only)
  if [ -n "$P_NAME" ]; then
    local t1 c1; t1=$(date +%s.%N); cpu > "$W/.cpu"; c1=$(cat "$W/.cpu")
    awk -v n="$P_NAME" -v t0="$P_T0" -v t1="$t1" -v c0="$P_C0" -v c1="$c1" -v l="$P_L0" \
      'BEGIN { printf "%s\t%.1f\t%.1f\t%s\n", n, t1 - t0, c1 - c0, l }' >> "$TIMES"
  fi
  P_NAME=$1; P_T0=$(date +%s.%N); cpu > "$W/.cpu"; P_C0=$(cat "$W/.cpu"); P_L0=$(cut -d' ' -f1 /proc/loadavg)
  [ -n "$1" ] && echo "gate: [$(date +%T)] $1"
  return 0
}

# 1. the work tree: a copy of the tree under test's Lean projects, generated-library inputs and
#    demos, keeping the built .lake/ directories (Lake writes into every package it builds)
phase sync
lakes() { find "$1" -name .lake -type d -prune 2>/dev/null; }
if [ "${GATE_CLEAN:-0}" = 1 ]; then
  lakes "$T" | xargs -r rm -rf
  rm -rf "$W/target"
elif [ -n "${GATE_SEED:-}" ] && [ -z "$(lakes "$T")" ]; then
  (cd "$GATE_SEED/k2lean" && find . -name .lake -type d -prune) | while read -r l; do
    mkdir -p "$T/$(dirname "$l")"; cp -a "$GATE_SEED/k2lean/$l" "$T/$l"
  done
  # not the Cargo target: its test binaries hold the seed's absolute binary path
  # (CARGO_BIN_EXE_k2lean) and Cargo would not rebuild them; a clean Cargo build takes seconds
fi
for d in lean demos generated; do
  mkdir -p "$T/$d"
  rsync -a --delete --exclude=.lake "$ROOT/$d/" "$T/$d/"
done
ok sync

# 2. the generator, built in the workspace around the tree under test, and its unit and snapshot
#    tests (which read the fixtures of that tree)
phase generator
G=$W/target/release/k2lean
WS=$(cd "$ROOT/.." && pwd)
if cargo build --release --locked -p k2lean --manifest-path "$WS/Cargo.toml" > "$L/cargo-build.log" 2>&1; then ok cargo-build "$L/cargo-build.log"
else bad cargo-build "$L/cargo-build.log"; phase ""; python3 -I "$CHECK" check "$W" "$BASE" "$TIER"; exit 1; fi
if cargo test --release --locked -p k2lean --manifest-path "$WS/Cargo.toml" --no-fail-fast > "$L/cargo-test.log" 2>&1; then ok cargo-test "$L/cargo-test.log"
else bad cargo-test "$L/cargo-test.log"; fi
grep -E '^test result:' "$L/cargo-test.log" | awk '{ p += $4; f += $6 } END { printf "unit_passed = %d\nunit_failed = %d\n", p, f }' >> "$MEAS/run.toml"

# 3. the helpers the areas' phases (gate_AREA in tests/areas/AREA.sh) are written with
declare -A KC=()
kc() { # NAME: krust's compiled KORE of definition NAME (tests/libs.sh), once per run
  if [ -z "${KC[$1]:-}" ]; then
    if libs_kcompile "$1" > "$L/kcompile-$1.log" 2>&1; then ok "kcompile $1"; KC[$1]=0
    else bad "kcompile $1" "$L/kcompile-$1.log"; KC[$1]=1; fi
  fi
  return "${KC[$1]}"
}
genlib() { # DIR: the generator call (tests/libs.sh, shared with demos/regen.sh)
  libs_gen "$1" > "$L/gen-$1.log" 2>&1
}
lbuild() { # DIR LOGNAME TARGET...: lake build in a project, timed
  local dir=$1 log=$L/$2.log; shift 2
  (cd "$dir" && "$RT" lake build "$@") > "$log" 2>&1
}
lib_open() { # DIR: the library's directory and open-obligation list (emptied under GATE_RETRY_OPEN)
  mkdir -p "$GEN/$1"; touch "$GEN/$1/open-obligations.txt"
  # a retry keeps the obligations marked refuted (a proof of one cannot exist) and the comments
  if [ "${GATE_RETRY_OPEN:-0}" = 1 ]; then
    grep -E '^#| \| refuted( hand)?( *#.*)?$' "$GEN/$1/open-obligations.txt" > "$GEN/$1/open-obligations.txt.keep" || true
    mv -f "$GEN/$1/open-obligations.txt.keep" "$GEN/$1/open-obligations.txt"
  fi
  return 0
}
seed_lake() { # DIR FROM: start library DIR's build from library FROM's (same Terms … Equations)
  mkdir -p "$GEN/$1"
  [ -d "$GEN/$1/.lake" ] || { [ -d "$GEN/$2/.lake" ] && cp -a "$GEN/$2/.lake" "$GEN/$1/.lake"; }
  return 0
}
# a library: a failed equation proof becomes an open obligation (`open-from-log`), then the library
# is regenerated; the gate compares the resulting open set with the baseline
eqns() { # DIR NAME: build NAME.Equations; on failure turn the failed proofs into open obligations,
  # regenerate and retry (twice at most)
  local d=$1 n=$2 o=$GEN/$1 k
  for k in 1 2 3; do
    lbuild "$o" "build-$d-eqns-$k" "$n.Equations" && { ok "build $n.Equations" "$L/build-$d-eqns-$k.log"; return 0; }
    [ "$k" = 3 ] && break
    "$G" open-from-log "$o/$n/Equations.lean" "$L/build-$d-eqns-$k.log" "$o/open-obligations.txt" >> "$L/gen-$d.log" 2>&1
    genlib "$d" || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  done
  bad "build $n.Equations" "$L/build-$d-eqns-3.log"; return 1
}
lib() { # DIR NAME [COMMAND...]: generate (then run COMMAND), Equations, the whole library, its guard
  local d=$1 n=$2 o=$GEN/$1; shift 2
  phase "lib $d"
  lib_open "$d"
  genlib "$d" || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  [ $# -gt 0 ] && "$@"
  eqns "$d" "$n" || return 1
  lbuild "$o" "build-$d" "$n" || { bad "build $d" "$L/build-$d.log"; return 1; }
  ok "build $d" "$L/build-$d.log"
  lbuild "$o" "build-$d-guard" "${n}Test.Axioms" || { bad "guard $d" "$L/build-$d-guard.log"; return 1; }
  ok "guard $d" "$L/build-$d-guard.log"
  # the fuel twins (`NS/Fuel.lean`, not imported by the library's root), with their axiom guard
  if [ -f "$o/$n/Fuel.lean" ]; then
    lbuild "$o" "build-$d-fuel" "$n.Fuel" || { bad "fuel $d" "$L/build-$d-fuel.log"; return 1; }
    ok "fuel $d" "$L/build-$d-fuel.log"
  fi
}
partlib() { # DIR TARGET: a library generated and built only as far as TARGET (what a demo needs)
  local d=$1
  mkdir -p "$GEN/$d"; touch "$GEN/$d/open-obligations.txt"
  if genlib "$d"; then
    if lbuild "$GEN/$d" "build-$d" "$2"; then ok "build $d" "$L/build-$d.log"
    else bad "build $d" "$L/build-$d.log"; fi
  else bad "gen $d" "$L/gen-$d.log"; fi
}
rel() { # NS: the relation of demo NS (tests/libs.sh)
  libs_relate "$1" > "$L/relate-$1.log" 2>&1 && ok "relate $1" || bad "relate $1" "$L/relate-$1.log"
}
scaffold() { # STEP COMMAND...: one generator call of a demo (tests/areas/AREA.sh)
  local n=$1 log=$L/${1// /-}.log; shift
  "$@" > "$log" 2>&1 && ok "$n" "$log" || bad "$n" "$log"
}
dbuild() { # PROJECT: build demo PROJECT; its axiom guards are `#k2l_assert_axioms` commands inside it
  if lbuild "$D/$1" "build-$1"; then ok "build $1" "$L/build-$1.log"; else bad "build $1" "$L/build-$1.log"; fi
}
# `k2lean diff` of each library's last generation in the tree under test (its generated/, when
# demos/regen.sh has written one there; git tracks only the open lists) against the regenerated
# one, with the hand-written references in the demos and the kind 1 open-case lists: informational
# (measured/diff-LIB.{txt,toml}; gate-check prints a NOTE when they differ)
diffs() { # DIR...: of those libraries this tier runs
  local d n
  for d in "$@"; do
    runs lib "$d" || continue
    n=$(libs_name "$d") || continue
    [ -f "$ROOT/generated/$d/$n/Preserves.lean" ] && [ -f "$GEN/$d/$n/Preserves.lean" ] || continue
    "$G" diff "$ROOT/generated/$d" "$GEN/$d" --hand "$D" --hand "$GEN/$d" --toml "$MEAS/diff-$d.toml" \
      > "$MEAS/diff-$d.txt" 2>&1
    [ $? -le 1 ] && ok "diff $d" "$MEAS/diff-$d.txt" || bad "diff $d" "$MEAS/diff-$d.txt"
  done
}

# 4. the areas, in order: each runs the entries of its own that this tier includes
for a in $LIBS_AREAS; do "gate_$a"; done

# 5. measure and compare
phase check
python3 -I "$CHECK" check "$W" "$BASE" "$TIER"
rc=$?
phase ""
column -t -s "$(printf '\t')" "$TIMES" | sed 's/^/gate: time  /'
exit $rc
