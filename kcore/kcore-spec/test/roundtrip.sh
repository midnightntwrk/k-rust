#!/usr/bin/env bash
# The native round trip (`kcore roundtrip`) over the f2-examples texts and the example packages'
# inputs, each verdict (exact, modulo, differs, cannot) compared with test/roundtrip.expected.
# Each text under a 12 GiB memory scope. Usage: test/roundtrip.sh  (`kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
out=.lake/roundtrip.txt; : > "$out"
for f in f2-examples/*.kore examples/*/*/definition.kore; do
  systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 600 \
    .lake/build/bin/kcore roundtrip "$f" >> "$out" 2>&1
done
grep -v '^  ' "$out" | awk '{sub(":$", "", $2); print $1, $2}' > .lake/roundtrip.verdicts
if diff test/roundtrip.expected .lake/roundtrip.verdicts; then
  echo "round trip: $(cut -d' ' -f1 .lake/roundtrip.verdicts | sort | uniq -c | tr '\n' ' ')(as expected; details in $out)"
else echo "round trip: verdicts changed (above; details in $out)"; exit 1; fi
