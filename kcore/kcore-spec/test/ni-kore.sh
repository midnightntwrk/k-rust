#!/usr/bin/env bash
# The two KORE texts of kimp's noninterference (examples/kimp, examples/imp-sec, examples/kimp-ni): kimp itself (Runtime Verification's
# imp-semantics, through the k-rust checkout's `imp-semantics` link) and its security checker
# (f2-examples/imp-sec.k), compiled by krust as the corpus is (findings/work/compile.py), into
# f2-examples/kimp.kore and f2-examples/imp-sec.kore. Needs target/release/krust in the checkout.
set -eu
K=$(cd "$(dirname "$0")/.." && pwd); KR=$(cd "$K/../../.." && pwd)
KIMP=$KR/imp-semantics/src/kimp/kdist/imp-semantics
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
run() { timeout 600 prlimit --as=$((12*1024**3)) "$KR/target/release/krust" kcompile "$@" -w none -I "$KIMP" >/dev/null; }
run "$KIMP/imp.k" --main-module IMP --syntax-module IMP-SYNTAX -o "$T/kimp"
run "$K/f2-examples/imp-sec.k" --main-module IMP-SEC --syntax-module IMP-SEC-SYNTAX -o "$T/sec"
cp "$T/kimp/definition.kore" "$K/f2-examples/kimp.kore"
cp "$T/sec/definition.kore" "$K/f2-examples/imp-sec.kore"
ls -l "$K/f2-examples/kimp.kore" "$K/f2-examples/imp-sec.kore" | awk '{print $5, $9}'
