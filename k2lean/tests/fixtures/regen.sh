#!/usr/bin/env bash
# Recompile the generator's K fixtures with krust and rewrite the snapshot files.
# Each fixture is a directory NAME/ with NAME.k (main module NAME in upper case, syntax module
# NAME-SYNTAX), the compiled definition.kore and runtime.json, its syntax definition
# syntaxDefinition.kore (the symbols' concrete syntax, by which `k2lean relate` pairs the symbols of
# two definitions; definition.kore carries none), the initial configurations of its
# witness programs (witnesses/NAME.kore beside each program), and, for the snapshot fixtures,
# expected/, the Lean project that `k2lean gen` writes for it
# (k2lean/crates/k2lean/tests/snapshots.rs compares a fresh generation with it).
# diff/ is the fixture of `k2lean diff`: old.k and new.k, two versions of one definition, compiled
# into old/ and new/ (no snapshot; k2lean/crates/k2lean/tests/cli.rs generates and compares them).
#
#   k2lean/tests/fixtures/regen.sh            recompile every fixture, then bless the snapshots
#   k2lean/tests/fixtures/regen.sh --bless    only bless (after an intended generator change)
#
# Blessing runs `cargo test -p k2lean --test snapshots` with K2LEAN_BLESS=1; review the diff of
# expected/. krust writes the absolute path of each source file into the KORE `Source` attribute;
# the fixtures' own paths are rewritten relative to the repository root, so that the checked-in
# files do not depend on where the checkout is (the generator reads only the file's base name).
#
# Environment: KRUST (default target/release/krust of this checkout), K_BUILTIN (K's builtin
# include directory; default k/result/include/kframework/builtin, the reference K of
# README.md, "Compatibility evidence").
set -euo pipefail
F=$(cd "$(dirname "$0")" && pwd)
R=$(cd "$F/../../.." && pwd)
KRUST=${KRUST:-$R/target/release/krust}
K_BUILTIN=${K_BUILTIN:-$R/k/result/include/kframework/builtin}
kc() { # FILE.k MODULE OUTDIR: krust's definition.kore, runtime.json and syntaxDefinition.kore of FILE.k into OUTDIR
  mkdir -p "$3"
  "$KRUST" kcompile "$1" --main-module "$2" --syntax-module "$2-SYNTAX" \
    --output-directory "$3/out" --builtin-directory "$K_BUILTIN"
  # each witness program OUTDIR/witnesses/NAME.EXT (`k2lean confluence --witnesses`): its initial
  # configuration, NAME.kore (krust's `krun --depth 0`, parsed at the sort of `$PGM`)
  local p sort
  for p in "$3"/witnesses/*; do
    case $p in *.kore | *'*') continue ;; esac
    sort=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["configuration_variables"]["PGM"])' "$3/out/runtime.json")
    "$KRUST" krun --definition "$3/out" --depth 0 --sort "$sort" "$p" > "${p%.*}.kore"
  done
  mv "$3/out/definition.kore" "$3/out/runtime.json" "$3/out/syntaxDefinition.kore" "$3/"
  rm -rf "$3/out"
  sed -i "s|Source($F/|Source(k2lean/tests/fixtures/|g" "$3/definition.kore" "$3/runtime.json" "$3/syntaxDefinition.kore"
}
if [ "${1:-}" != --bless ]; then
  [ -x "$KRUST" ] || { echo "regen.sh: needs krust at $KRUST (set KRUST)" >&2; exit 2; }
  for d in "$F"/*/; do
    d=${d%/}
    n=$(basename "$d"); up=$(echo "$n" | tr a-z A-Z)
    [ -f "$d/$n.k" ] && kc "$d/$n.k" "$up" "$d"
  done
  # the `k2lean diff` fixture (tests/cli.rs): two generations of one definition, DIFF
  for v in old new; do kc "$F/diff/$v.k" DIFF "$F/diff/$v"; done
fi
cd "$R"
K2LEAN_BLESS=1 cargo test -p k2lean --locked --test snapshots
