#!/usr/bin/env bash
# k2lean's regression gate.
# Regenerates every library and demonstration from the K sources with the generator under test,
# builds them in a scratch work tree, and compares what it measures with tests/baseline.toml.
#
#   k2lean/tests/gate.sh light    generator unit and snapshot tests; kimp (goldens, step traces
#                                 against krust and the K LLVM backend), kimp-d2 (kimp's determinism
#                                 along the rule index, `--det2`), krsimp, kmut, imptypes; the
#                                 demos ImpRel, ImpTypes, ImpMut, KrsImpTyping, ImpWrites (a kind 2
#                                 invariant that walks <k>); the kind 1 invariants of kimpinv (two K
#                                 functions of demos/k/kimp-inv), kimpfold and kimptop (the same
#                                 definition: a fold with a parameter, the top-cell form), kimpkeys
#                                 (the walkthrough of docs/invariants.md, demos/k/kimp-keys),
#                                 kimpkeys-hand (the same with one case taken from its hand
#                                 module), nested (a cell inside two nested cell maps,
#                                 tests/fixtures/nested) and krsimp (the KRS sidecar), and the
#                                 negative check: on KRS IMP with an
#                                 ill-typed `assign`, the generated proof of the declared cell type
#                                 must fail at that rule; the kind 2 template (`k2lean new-invariant`
#                                 for kimp, built), and `k2lean diff` of every library against the
#                                 tree's last generation, when it has one
#   k2lean/tests/gate.sh heavy    light, then SIMPLE (acceptance against krust), the SIMPLE
#                                 invariants (the kind 1 `holdsOk@holds`, lifted over the <thread>
#                                 cell map, of simpleinv, demos/k/simple-inv, and "every store value
#                                 is a Val or undefined" as a cell function, simplestore, and as a function of
#                                 the top cell <T>, simplet; the kind 2 demo SimpleEnv), kimp-claims
#                                 (claims.toml, krust kprove, kc_auto statistics, three replays) and
#                                 the demo ImpRelClaims (a kimp claim transferred to KRS IMP along the
#                                 bisimulation)
#   k2lean/tests/gate.sh arity    generator unit and snapshot tests, then kimp and SIMPLE in the
#                                 arity-indexed term universe (`gen --arity-terms`, libraries kimp-ar
#                                 and simple-ar): built with their axiom guards, kimp's goldens and
#                                 step traces, SIMPLE's cases against krust; their recorded outputs
#                                 must equal the default encoding's (expected/)
#   k2lean/tests/gate.sh accept   make the last run's measurements the baseline (tests/baseline.toml
#                                 and tests/expected/); a light run replaces only the light entries,
#                                 an arity run only the arity entries (and no recorded output)
#
# Exit status: 0 the tier passes; 1 a regression (the `FAIL` lines say which); 2 a setup error.
# A clean light run builds eight Lean libraries and six Lean projects: on 2026-10-24, on a shared
# 32-CPU host, its part of a clean heavy run took 809 s wall and 1,198 s of CPU under a load of 8 to
# 21 (4.0 GB peak in a light run); the clean heavy run took 1,661 s wall, 2,389 s of CPU and 4.7 GB,
# and a clean arity run 457 s and 679 s under a load of 20 to 33. A rerun rebuilds only what changed
# (26 s light, 50 s heavy, measured before the kimpkeys libraries and ImpWrites were added).
#
# Needs: krust (a release build), the K release's `kompile` with its LLVM backend (kimp's step
# traces), the K sources and kimp's sources at the pins of scripts/reference-differential.toml
# (README.md, "Compatibility evidence"), cargo, lake (elan) and python3 >= 3.11 on PATH.
#
# Environment (paths may be relative to the current directory):
#   GATE_ROOT=DIR       the k2lean directory under test (default: the one holding this script); it
#                       needs lean/, demos/ and generated/ (the open-obligation lists), and its
#                       parent must be the k-rust workspace the generator is built in, so a
#                       worktree or a copy of the whole checkout can be tested
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
#   GATE_RETRY_OPEN=1   start every library from an empty open-obligation list, so every open
#                       obligation is attempted again (finds removals; rebuilds every Equations)
#   GATE_BASELINE=FILE  the baseline (default tests/baseline.toml next to this script); its
#                       expected outputs are in expected/ beside it
#   GATE_CACHE=DIR      outputs cached by the hash of their inputs (default target/k2lean-gate/cache
#                       in the checkout holding this script): kimp's K LLVM interpreter, SIMPLE's
#                       krust-derived cases; GATE_CLEAN keeps it
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
BASE=${GATE_BASELINE:-$SELF/tests/baseline.toml}
ROOT=$(cd "${GATE_ROOT:-$SELF}" && pwd)
if [ "$ROOT" = "$SELF" ]; then name=main; else name=$(basename "$(dirname "$ROOT")")-$(printf %s "$ROOT" | sha256sum | cut -c1-8); fi
W=${GATE_WORK:-$REPO/target/k2lean-gate/work/$name}
CACHE=${GATE_CACHE:-$REPO/target/k2lean-gate/cache}
mkdir -p "$W" "$CACHE"
W=$(cd "$W" && pwd) CACHE=$(cd "$CACHE" && pwd)

case $TIER in
  light|heavy|arity) ;;
  accept) exec python3 -I "$CHECK" accept "$W" "$BASE" ;;
  *) sed -n '2,/^set -uo/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 2 ;;
esac

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
if [ "$TIER" != light ]; then
  [ -d "$SD" ] || need "SIMPLE's sources at $SD (set GATE_K_CHECKOUT)"
fi
if [ "$TIER" = heavy ]; then
  [ -d "$SPECS" ] || need "kimp's claims at $SPECS (set GATE_IMP_CHECKOUT)"
fi
for t in cargo lake python3 rsync; do command -v "$t" > /dev/null || need "$t on PATH"; done
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
# the generator calls (shared with demos/regen.sh): the tree under test's tests/libs.sh, else this one's
LIBS=$ROOT/tests/libs.sh; [ -f "$LIBS" ] || LIBS=$SELF/tests/libs.sh
# shellcheck source=libs.sh
. "$LIBS"
DEMOS=$D KRS=$D/k/krs-imp FIXTURES=$ROOT/tests/fixtures
kore_dir() { echo "$KO/$1"; }
rm -rf "$L" "$MEAS"
mkdir -p "$L" "$MEAS" "$KO"
STATUS=$MEAS/status.tsv
TIMES=$MEAS/times.tsv
printf 'step\tresult\tlog\n' > "$STATUS"
printf 'phase\twall_s\tcpu_s\tload_at_start\n' > "$TIMES"
printf 'tier = "%s"\nroot = "%s"\nkimp = "%s"\nstarted = "%s"\n' "$TIER" "$ROOT" "$KIMP" "$(date -Is)" > "$MEAS/run.toml"

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

# 3. compiled KORE (krust) and K's LLVM interpreter of kimp, a second executor that the step
#    traces compare krust and the Lean semantics with
phase krust
kc() { # NAME: krust's compiled KORE of NAME (tests/libs.sh)
  if libs_kcompile "$1" > "$L/kcompile-$1.log" 2>&1; then ok "kcompile $1"
  else bad "kcompile $1" "$L/kcompile-$1.log"; return 1; fi
}
kc kimp
kc kimp-verif
if [ "$TIER" != arity ]; then
  kc kimp-inv
  kc kimp-keys
  kc imp-typing
  kc kmut
fi
phase llvm
key=$(cd "$KIMP" && find . -type f | sort | xargs sha256sum | sha256sum | cut -c1-12)
LLVM=$CACHE/kimp-llvm-$key
if [ ! -x "$LLVM/interpreter" ]; then
  rm -rf "$LLVM"
  if K_OPTS="-Xmx4096m -Xss4m" "$KOMPILE" "$KIMP/imp.k" --backend llvm --main-module IMP --syntax-module IMP-SYNTAX \
       --output-definition "$LLVM" --warnings none -I "$KIMP" > "$L/kompile-llvm.log" 2>&1; then ok kompile-llvm
  else bad kompile-llvm "$L/kompile-llvm.log"; fi
fi

# 4. the libraries; a failed equation proof becomes an open obligation (`open-from-log`), then the
#    library is regenerated; the gate compares the resulting open set with the baseline
genlib() { # DIR: the generator call (tests/libs.sh, shared with demos/regen.sh)
  libs_gen "$1" > "$L/gen-$1.log" 2>&1
}
lbuild() { # DIR LOGNAME TARGET...: lake build in a project, timed
  local dir=$1 log=$L/$2.log; shift 2
  (cd "$dir" && "$RT" lake build "$@") > "$log" 2>&1
}
goldens() { # DIR: the goldens and traces of kimp's library DIR (kimp or kimp-ar)
  libs_goldens "$W/goldens-tmp" "$LLVM/interpreter" "$1" > "$L/goldens.log" 2>&1
}
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
lib() { # DIR NAME
  local d=$1 n=$2 o=$GEN/$1
  phase "lib $d"
  mkdir -p "$o"; touch "$o/open-obligations.txt"
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$o/open-obligations.txt"
  genlib "$d" || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  if [ "$d" = kimp ] || [ "$d" = kimp-ar ]; then
    if goldens "$d"; then ok goldens "$L/goldens.log"; else bad goldens "$L/goldens.log"; fi
  fi
  eqns "$d" "$n" || return 1
  lbuild "$o" "build-$d" "$n" || { bad "build $d" "$L/build-$d.log"; return 1; }
  ok "build $d" "$L/build-$d.log"
  lbuild "$o" "build-$d-guard" "${n}Test.Axioms" || { bad "guard $d" "$L/build-$d-guard.log"; return 1; }
  ok "guard $d" "$L/build-$d-guard.log"
}
kimp_tests() { # DIR: build and run kimp's test driver of library DIR (goldens and traces)
  phase "$1 tests"
  if lbuild "$GEN/$1" "build-$1-test" kimp-test; then
    "$GEN/$1/.lake/build/bin/kimp-test" --toml "$MEAS/goldens.toml" > "$MEAS/kimp-test.out" 2> "$L/$1-test.err" \
      && ok "$1-test" "$MEAS/kimp-test.out" || bad "$1-test" "$MEAS/kimp-test.out"
  else bad "build $1-test" "$L/build-$1-test.log"; fi
}
if [ "$TIER" != arity ]; then
lib kimp KImp && kimp_tests kimp
# kimp with determinism along the rule index (tests/libs.sh): Terms … Equations are kimp's, so
# its build starts from kimp's (only Determinism and the guard differ)
mkdir -p "$GEN/kimp-d2"
[ -d "$GEN/kimp-d2/.lake" ] || { [ -d "$GEN/kimp/.lake" ] && cp -a "$GEN/kimp/.lake" "$GEN/kimp-d2/.lake"; }
lib kimp-d2 KImp
lib krsimp KrsImp
lib kmut KMut
lib imptypes KImpTypes

# 4b. kind 1 invariants: `{ns}/Invariants.lean`. A rule case that `k2l_preserve` does not close
#     becomes an open case (`open-from-log` into open-invariant-cases.txt) and the library is
#     regenerated, so the case is then taken from the hand module, as for equations.
invcases() { # DIR NAME: build NAME.Invariants, at most three attempts; the last log is build-DIR-inv.log
  local d=$1 n=$2 o=$GEN/$1 k
  for k in 1 2 3; do
    if lbuild "$o" "build-$d-inv-$k" "$n.Invariants"; then
      cp "$L/build-$d-inv-$k.log" "$L/build-$d-inv.log"; ok "invariant $d" "$L/build-$d-inv.log"; return 0
    fi
    cp "$L/build-$d-inv-$k.log" "$L/build-$d-inv.log"
    [ "$k" = 3 ] && break
    "$G" open-from-log "$o/$n/Invariants.lean" "$L/build-$d-inv-$k.log" "$o/open-invariant-cases.txt" >> "$L/gen-$d.log" 2>&1
    genlib "$d" >> "$L/gen-$d.log" 2>&1 || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  done
  bad "invariant $d" "$L/build-$d-inv.log"; return 1
}
inv_reset() { # DIR: GATE_RETRY_OPEN also retries the open invariant cases
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/$1/open-invariant-cases.txt"
  return 0
}
phase "invariant krsimp"
[ -f "$GEN/krsimp/KrsImp/Invariants.lean" ] && { inv_reset krsimp; invcases krsimp KrsImp; }
phase "lib kimpinv"
# kimp with the K function `envOk` (demos/k/kimp-inv/imp-inv.k): only what Invariants.lean needs
# (its Equations, for the K equations it unfolds), not Adequacy or Determinism
if [ -f "$KO/kimp-inv/definition.kore" ]; then
  mkdir -p "$GEN/kimpinv"; touch "$GEN/kimpinv/open-obligations.txt"
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/kimpinv/open-obligations.txt"
  inv_reset kimpinv
  if genlib kimpinv; then
    eqns kimpinv KImpInv && invcases kimpinv KImpInv
  else bad "gen kimpinv" "$L/gen-kimpinv.log"; fi
fi
# kimp with the K function `envKeysOk` (demos/k/kimp-keys): the walkthrough of docs/invariants.md,
# §3, every case by `k2l_preserve`; then kimpkeys-hand, the same library (so its build starts from
# kimpkeys') whose tracked open-invariant-cases.txt lists one case, proved in its tracked hand
# module KImpKeys/InvariantsHand.lean: the kind 1 hand path, and an edit of the hand module is
# checked by this build, not by the sources check
for d in kimpkeys kimpkeys-hand; do
  phase "lib $d"
  [ -f "$KO/kimp-keys/definition.kore" ] || continue
  mkdir -p "$GEN/$d"; touch "$GEN/$d/open-obligations.txt"
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/$d/open-obligations.txt"
  [ "$d" = kimpkeys ] && inv_reset "$d"
  [ "$d" = kimpkeys-hand ] && [ ! -d "$GEN/$d/.lake" ] && [ -d "$GEN/kimpkeys/.lake" ] && cp -a "$GEN/kimpkeys/.lake" "$GEN/$d/.lake"
  if genlib "$d"; then
    eqns "$d" KImpKeys && invcases "$d" KImpKeys
  else bad "gen $d" "$L/gen-$d.log"; fi
done
# the other shapes of kind 1 invariant over kimpinv's definition: a fold with a parameter
# (kimpfold) and the top-cell form (kimptop); their Terms … Equations are kimpinv's, so each starts
# from its build
for d in kimpfold kimptop; do
  phase "lib $d"
  [ -f "$KO/kimp-inv/definition.kore" ] || continue
  mkdir -p "$GEN/$d"; touch "$GEN/$d/open-obligations.txt"
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/$d/open-obligations.txt"
  [ -d "$GEN/$d/.lake" ] || { [ -d "$GEN/kimpinv/.lake" ] && cp -a "$GEN/kimpinv/.lake" "$GEN/$d/.lake"; }
  inv_reset "$d"
  if genlib "$d"; then
    eqns "$d" KImpInv && invcases "$d" KImpInv
  else bad "gen $d" "$L/gen-$d.log"; fi
done
# a cell inside two nested cell maps (tests/fixtures/nested): only what Invariants.lean needs
phase "lib nested"
mkdir -p "$GEN/nested"; touch "$GEN/nested/open-obligations.txt"
[ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/nested/open-obligations.txt"
inv_reset nested
if genlib nested; then
  eqns nested KNested && invcases nested KNested
else bad "gen nested" "$L/gen-nested.log"; fi
phase "negative"
# KRS IMP with an ill-typed `assign` (tests/krs-imp-ill-typed.py): the sidecar's `Preserved` proof
# must fail, and name the rule (as the open case and in the build error); measured/negative.toml
# records what happened
NEG=$T/negative/krsimp-ill-typed
mkdir -p "$NEG"
rm -rf "$NEG/KrsImp"
[ -d "$NEG/.lake" ] || { [ -d "$GEN/krsimp/.lake" ] && cp -a "$GEN/krsimp/.lake" "$NEG/.lake"; }  # same Terms.lean
cp "$GEN/krsimp/open-obligations.txt" "$NEG/open-obligations.txt"
: > "$NEG/open-invariant-cases.txt"
neg_built=false
if libs_gen_ill_typed "$NEG" > "$L/gen-ill-typed.log" 2>&1; then
  ok "gen ill-typed" "$L/gen-ill-typed.log"
  for k in 1 2; do
    if lbuild "$NEG" "build-ill-typed-$k" KrsImp.Invariants; then neg_built=true; break; fi
    [ "$k" = 2 ] && break
    "$G" open-from-log "$NEG/KrsImp/Invariants.lean" "$L/build-ill-typed-$k.log" "$NEG/open-invariant-cases.txt" >> "$L/gen-ill-typed.log" 2>&1
    libs_gen_ill_typed "$NEG" >> "$L/gen-ill-typed.log" 2>&1 || bad "gen ill-typed" "$L/gen-ill-typed.log"
  done
  last=$(ls "$L"/build-ill-typed-*.log | sort | tail -1)
  python3 -I - "$NEG/open-invariant-cases.txt" "$last" "$neg_built" > "$MEAS/negative.toml" <<'PY'
import re, sys
cases, log, built = sys.argv[1], sys.argv[2], sys.argv[3] == "true"
opened = []
for l in open(cases):
    l = l.strip()
    if l and not l.startswith("#"):
        opened.append(l.split(" | ")[0])
errors = [l for l in open(log) if re.match(r"\s*error: ", l)]
named = sorted({n for l in errors for n in re.findall(r"«[^»]*»", l)})
q = lambda s: '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
print("[krsimp-ill-typed]")
print(f"builds = {'true' if built else 'false'}")
print(f"open = [{', '.join(q(x) for x in sorted(opened))}]")
print(f"error_names = [{', '.join(q(x) for x in named)}]")
print(f"first_error = {q(errors[0].strip()) if errors else q('')}")
PY
  ok "negative ill-typed" "$MEAS/negative.toml"
else bad "gen ill-typed" "$L/gen-ill-typed.log"; fi

# 4c. `k2lean diff` of each library's last generation in the tree under test (its generated/, when
#     demos/regen.sh has written one there; git tracks only the open lists) against the regenerated
#     one, with the hand-written references in the demos and the kind 1 open-case lists:
#     informational (measured/diff-LIB.{txt,toml}; gate-check prints a NOTE when they differ)
diffs() { # DIR...
  local d n
  for d in "$@"; do
    n=$(libs_name "$d") || continue
    [ -f "$ROOT/generated/$d/$n/Preserves.lean" ] && [ -f "$GEN/$d/$n/Preserves.lean" ] || continue
    "$G" diff "$ROOT/generated/$d" "$GEN/$d" --hand "$D" --hand "$GEN/$d" --toml "$MEAS/diff-$d.toml" \
      > "$MEAS/diff-$d.txt" 2>&1
    [ $? -le 1 ] && ok "diff $d" "$MEAS/diff-$d.txt" || bad "diff $d" "$MEAS/diff-$d.txt"
  done
}
phase diff
diffs kimp krsimp kmut imptypes kimpinv kimpkeys kimpfold kimptop nested

# 5. the relations (generated files of ImpRel, ImpTypes, ImpMut) and the five demo projects; their
#    axiom guards are `#k2l_assert_axioms` commands inside them
phase demos
rel() { # NS (tests/libs.sh)
  libs_relate "$1" > "$L/relate-$1.log" 2>&1 && ok "relate $1" || bad "relate $1" "$L/relate-$1.log"
}
rel ImpRel
rel ImpTypes
rel ImpMut
for p in ImpRel ImpTypes ImpMut KrsImpTyping ImpWrites; do
  if lbuild "$D/$p" "build-$p"; then ok "build $p" "$L/build-$p.log"; else bad "build $p" "$L/build-$p.log"; fi
done

# 5b. the kind 2 template: the skeleton `k2lean new-invariant` writes for kimp, rewritten on every
#     run (the command never overwrites a file, so the skeleton's files are deleted first; .lake/
#     and the manifest are kept), built like a demo (demo.Kind2Template)
phase "kind2 template"
K2T=$W/kind2/KImpTpl
mkdir -p "$K2T"
find "$K2T" -name .lake -prune -o -name '*.lean' -type f -exec rm -f {} +
rm -f "$K2T/lean-toolchain"
if "$G" new-invariant --lib "$GEN/kimp" --out "$K2T" --name KImpTpl > "$L/kind2-new.log" 2>&1; then
  ok "new-invariant kimp" "$L/kind2-new.log"
  if lbuild "$K2T" build-Kind2Template; then ok "build Kind2Template" "$L/build-Kind2Template.log"
  else bad "build Kind2Template" "$L/build-Kind2Template.log"; fi
else bad "new-invariant kimp" "$L/kind2-new.log"; fi
fi # not arity

# 6. heavy: SIMPLE and the kimp claims
lib_simple() { # DIR (simple, simple-ar): generate, cases, build, guard, run the cases, acceptance table
  local d=$1 o=$GEN/$1
  mkdir -p "$o"; touch "$o/open-obligations.txt"
  [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$o/open-obligations.txt"
  genlib "$d" || { bad "gen $d" "$L/gen-$d.log"; return 1; }
  # the cases' expected results come from krust runs (about a minute); they are cached under the
  # hash of everything they depend on: the compiled definition, krust, the generator, the tests
  local key; key=$( { sha256sum "$KO/simple/definition.kore" "$KRUST" "$G"; printf '%s\n' "${LIBS_SIMPLE_CASES[@]}";
    cat "$SD"/tests/*/*.simple* 2>/dev/null; } | sha256sum | cut -c1-16)
  local cached=$CACHE/simple-cases-$key.lean
  if [ -f "$cached" ]; then
    cp "$cached" "$o/KSimpleTest/Cases.lean"; echo "cached $cached" > "$L/cases-$d.log"
  else
    libs_cases "$o/KSimpleTest/Cases.lean" > "$L/cases-$d.log" 2>&1 \
      || { bad "cases $d" "$L/cases-$d.log"; return 1; }
    cp "$o/KSimpleTest/Cases.lean" "$cached"
  fi
  eqns "$d" KSimple || return 1
  lbuild "$o" "build-$d" KSimple || { bad "build $d" "$L/build-$d.log"; return 1; }
  ok "build $d" "$L/build-$d.log"
  lbuild "$o" "build-$d-guard" KSimpleTest.Axioms || { bad "guard $d" "$L/build-$d-guard.log"; return 1; }
  ok "guard $d" "$L/build-$d-guard.log"
  lbuild "$o" "build-$d-test" ksimple-test || { bad "build ksimple-test" "$L/build-$d-test.log"; return 1; }
  "$o/.lake/build/bin/ksimple-test" > "$L/$d-test.out" 2>&1
  python3 -I "$SELF/tests/simple-acceptance.py" "$L/$d-test.out" "$SD/tests" "$KRUST" "$KO/simple" \
    "$MEAS/simple-acceptance.toml" > "$MEAS/simple-acceptance.md" 2> "$L/simple-acceptance.err"
}
if [ "$TIER" = arity ]; then
  lib kimp-ar KImp && kimp_tests kimp-ar
  phase "lib simple-ar"
  if libs_kcompile simple > "$L/kcompile-simple.log" 2>&1; then
    ok "kcompile simple"
    libs_simple_cases
    lib_simple simple-ar && ok "simple-ar acceptance" "$MEAS/simple-acceptance.md"
  else bad "kcompile simple" "$L/kcompile-simple.log"; fi
fi
if [ "$TIER" = heavy ]; then
  phase "lib simple"
  if libs_kcompile simple > "$L/kcompile-simple.log" 2>&1; then
    ok "kcompile simple"
    libs_simple_cases
    lib_simple simple && ok "simple acceptance" "$MEAS/simple-acceptance.md"
    diffs simple
  else bad "kcompile simple" "$L/kcompile-simple.log"; fi

  # SIMPLE's invariants. Kind 1: SIMPLE with the K function `holdsOk` (demos/k/simple-inv), only
  # what Invariants.lean needs, as for kimpinv; its open cases come from the hand module.
  phase "lib simpleinv"
  if libs_kcompile simple-inv > "$L/kcompile-simple-inv.log" 2>&1; then
    ok "kcompile simple-inv"
    mkdir -p "$GEN/simpleinv"; touch "$GEN/simpleinv/open-obligations.txt"
    [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/simpleinv/open-obligations.txt"
    inv_reset simpleinv
    if genlib simpleinv; then
      eqns simpleinv KSimpleInv && invcases simpleinv KSimpleInv
    else bad "gen simpleinv" "$L/gen-simpleinv.log"; fi
    diffs simpleinv
    # "every store value is a Val or undefined" as a cell function (simplestore) and as a function of SIMPLE's
    # top cell `<T>` (simplet), over the same definition: they start from simpleinv's build
    for d in simplestore simplet; do
      phase "lib $d"
      mkdir -p "$GEN/$d"; touch "$GEN/$d/open-obligations.txt"
      [ "${GATE_RETRY_OPEN:-0}" = 1 ] && : > "$GEN/$d/open-obligations.txt"
      [ -d "$GEN/$d/.lake" ] || { [ -d "$GEN/simpleinv/.lake" ] && cp -a "$GEN/simpleinv/.lake" "$GEN/$d/.lake"; }
      inv_reset "$d"
      if genlib "$d"; then
        eqns "$d" KSimpleInv && invcases "$d" KSimpleInv
      else bad "gen $d" "$L/gen-$d.log"; fi
      diffs "$d"
    done
  else bad "kcompile simple-inv" "$L/kcompile-simple-inv.log"; fi
  # Kind 2: a Lean invariant over KSimple's configuration (demos/SimpleEnv), built like a demo
  phase "demo SimpleEnv"
  if lbuild "$D/SimpleEnv" build-SimpleEnv; then ok "build SimpleEnv" "$L/build-SimpleEnv.log"
  else bad "build SimpleEnv" "$L/build-SimpleEnv.log"; fi

  phase "kimp claims"
  OUT=$GEN/kimp-claims
  OWN=$T/demos/claims/specs
  spec() { # FILE MODULE DIR
    "$KRUST" kcompile "$1" --main-module "$2" --definition-module IMP-VERIFICATION --for-proving \
      --output-directory "$KO/$3" --builtin-directory "$BUILTIN" -I "$KIMP" -I "$(dirname "$1")" -w none \
      > "$L/kcompile-$3.log" 2>&1 || bad "kcompile $3" "$L/kcompile-$3.log"
  }
  spec "$SPECS/imp-simple-spec.k" IMP-SIMPLE-SPEC imp-simple-spec
  spec "$SPECS/imp-sum-spec.k" IMP-SUM-SPEC imp-sum-spec
  spec "$OWN/imp-ifs-uint64-spec.k" IMP-IFS-UINT64-SPEC imp-ifs-uint64-spec
  spec "$OWN/imp-two-sum-aux-spec.k" IMP-TWO-SUM-AUX-SPEC imp-two-sum-aux-spec
  spec "$OWN/imp-div0-spec.k" IMP-DIV0-SPEC imp-div0-spec
  {
    for d in imp-simple-spec:IMP-SIMPLE-SPEC imp-ifs-uint64-spec:IMP-IFS-UINT64-SPEC imp-two-sum-aux-spec:IMP-TWO-SUM-AUX-SPEC imp-div0-spec:IMP-DIV0-SPEC; do
      "$KRUST" kprove --compiled-definition "$KO/${d%%:*}" --main-module "${d##*:}" 2>&1 < /dev/null | grep '^claim' || true
    done
    "$KRUST" kprove --compiled-definition "$KO/imp-sum-spec" --main-module IMP-SUM-SPEC \
      --claim IMP-SUM-SPEC.sum-spec 2>&1 < /dev/null | grep '^claim' || true
    "$KRUST" kprove --compiled-definition "$KO/imp-sum-spec" --main-module IMP-SUM-SPEC \
      --claim IMP-SUM-SPEC.two-sum-spec --depth 300 2>&1 < /dev/null | grep -E '^claim|^  [a-z]' || true
  } > "$MEAS/kprove.txt"
  if "$G" claims --kore "$KO/kimp/definition.kore" \
      --spec "$KO/imp-simple-spec/definition.kore" --spec "$KO/imp-sum-spec/definition.kore" \
      --spec "$KO/imp-ifs-uint64-spec/definition.kore" --spec "$KO/imp-two-sum-aux-spec/definition.kore" --spec "$KO/imp-div0-spec/definition.kore" \
      --out "$OUT" --name KImpClaims --semantics KImp --semantics-path ../kimp --kclaims-path ../../lean/claims \
      --open "$T/demos/claims/kimp-open.txt" \
      --hand Hand --hand Replay.Addition2 --hand Replay.Branching --hand Replay.SumLoop > "$L/claims-gen.log" 2>&1; then
    ok "claims gen"
    cp "$T/demos/claims/hand/Hand.lean" "$OUT/KImpClaims/Hand.lean"
    cp "$OUT/claims.toml" "$MEAS/claims.toml"
    mkdir -p "$OUT/KImpClaims/Replay" "$MEAS/replay"
    "$KRUST" kore-rpc "$KO/imp-simple-spec/definition.kore" --module IMP-SIMPLE-SPEC --server-port 0 \
      > "$L/rpc.log" 2>&1 < /dev/null &
    RPC=$!
    trap 'kill $RPC 2>/dev/null || true' EXIT
    for _ in $(seq 100); do grep -q listening "$L/rpc.log" && break; sleep 0.1; done
    PORT=$(sed -n 's/.*listening on 127.0.0.1:\([0-9]*\).*/\1/p' "$L/rpc.log")
    replay() { # LABEL MODULE-FILE [--cut RULE]
      local label=$1 file=$2; shift 2
      (ulimit -v 4000000; "$G" claims replay --kore "$KO/kimp/definition.kore" \
        --spec "$KO/imp-simple-spec/definition.kore" --claim "IMP-SIMPLE-SPEC.$label" --port "$PORT" \
        --out "$OUT/KImpClaims/Replay/$file.lean" --skeleton "$MEAS/replay/$label.toml" "$@") > "$L/replay-$label.log" 2>&1 \
        && ok "replay $label" || bad "replay $label" "$L/replay-$label.log"
    }
    replay addition-2 Addition2
    replay branching Branching
    replay sum-loop SumLoop --cut IMP.while
    kill $RPC 2>/dev/null; wait $RPC 2>/dev/null; trap - EXIT
    if lbuild "$OUT" build-claims; then
      ok "build claims" "$L/build-claims.log"
      if lbuild "$OUT" build-claims-guard KImpClaimsTest; then ok "guard claims" "$L/build-claims-guard.log"
      else bad "guard claims" "$L/build-claims-guard.log"; fi
      grep -o 'KImpClaims[^ ]*\.holds depends on axioms: .*' "$L/build-claims-guard.log" > "$MEAS/axioms.txt" || true
      grep -o 'KImpClaims.Hand[^ ]* depends on axioms: .*' "$L/build-claims.log" >> "$MEAS/axioms.txt" || true
      grep -E 'kc_auto' "$L/build-claims.log" > "$MEAS/kc-auto-stats.txt" || true
    else bad "build claims" "$L/build-claims.log"; fi
  else bad "claims gen" "$L/claims-gen.log"; fi

  # a kimp claim transferred to the KRS IMP port along ImpRel's bisimulation (demos/ImpRelClaims),
  # built like a demo (demo.ImpRelClaims)
  phase "demo ImpRelClaims"
  if lbuild "$D/ImpRelClaims" build-ImpRelClaims; then ok "build ImpRelClaims" "$L/build-ImpRelClaims.log"
  else bad "build ImpRelClaims" "$L/build-ImpRelClaims.log"; fi
fi

# 7. measure and compare
phase check
python3 -I "$CHECK" check "$W" "$BASE" "$TIER"
rc=$?
phase ""
column -t -s "$(printf '\t')" "$TIMES" | sed 's/^/gate: time  /'
exit $rc
