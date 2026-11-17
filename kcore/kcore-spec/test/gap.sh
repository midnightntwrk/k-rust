#!/usr/bin/env bash
# The gap between a kompiled text and its print-back (TIE-1 D2, "Is the gap a defect?"): `kcore gap`
# on each text, by default f2-examples/ens.kompile.kore. For each it prints the text's sentences
# that `emit` does not write back and the emitted sentences the text lacks, each classified by
# cause with counts (KcoreGen.lean, the section "The gap between a text and its print-back"), and
# every text sentence of a kind with a direction (declarations, rewrite rules, the equations of the
# definition's functions, constructor and subsort axioms) that the definition read does not hold as
# written: a reader defect, named by its kind. Exit 1 when a text has such a sentence or is not
# read. Usage (from anywhere, `kcore` built): test/gap.sh [--all] [KORE...]   (--all: every
# sentence of the gap with its cause)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
all=()
if [ "${1:-}" = "--all" ]; then all=(--all); shift; fi
[ $# -gt 0 ] || set -- f2-examples/ens.kompile.kore
rc=0
for f in "$@"; do
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 600 \
    .lake/build/bin/kcore gap "$f" "${all[@]}" || rc=1
done
exit $rc
