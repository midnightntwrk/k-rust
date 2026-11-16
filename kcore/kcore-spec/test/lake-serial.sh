#!/usr/bin/env bash
# Build KcoreSpec modules one at a time, in import order, each under a 12 GiB memory limit
# (a user systemd scope, MemoryMax=12G, no swap) with one thread (lakefile.toml passes -j1).
# Lake has no job limit, and parallel modules could together exceed free memory. The limit is on
# memory, not address space: under `prlimit --as` some modules fail to create a thread at a few
# GB resident (their reserved address space exceeds the cap). Usage: test/lake-serial.sh [MODULE...]
# (default: KcoreSpec, the whole library). Prints each module lake had to build, with seconds.
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
export LEAN_NUM_THREADS=1
roots=("$@"); [ ${#roots[@]} -eq 0 ] && roots=(KcoreSpec)
order=$(python3 -I - "${roots[@]}" <<'PY'
import os, re, sys
seen, out = set(), []
def visit(m):
    if m in seen: return
    seen.add(m)
    p = m.replace('.', '/') + '.lean'
    if not os.path.exists(p): return
    for line in open(p):
        r = re.match(r'import\s+(KcoreSpec\S*)', line)
        if r: visit(r.group(1))
    out.append(m)
for m in sys.argv[1:]: visit(m)
print('\n'.join(out))
PY
)
for m in $order; do
  t0=$(date +%s)
  log=$(timeout 3600 systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 \
    lake build "+$m" 2>&1); rc=$?
  t=$(( $(date +%s) - t0 ))
  if [ $rc -ne 0 ]; then echo "$m: FAILED ($t s)"; echo "$log" | grep -E "error|✖" | head -30; exit 1; fi
  echo "$log" | grep -q "Built $m\b\|Building $m\b" && echo "$m: built ($t s)"
done
echo "all built"
