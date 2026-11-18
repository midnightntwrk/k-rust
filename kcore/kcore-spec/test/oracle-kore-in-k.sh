#!/usr/bin/env bash
# `kcore oracle` on three cases of kk/agree-kore-in-k.jsonl (c03-nondet: several successors and
# finals; c08-undef-rhs-blocks: a configuration at which a rule applies with no result, U;
# c24-map-fn-pattern: `CoherentAll` not decided), one line per case
# `ID oracle:B reached:R N:n U:u coherent:C vs:V`, compared with test/oracle-kore-in-k.expected.
# Needs the kompiled texts in .lake/kore-in-k (test/README.md, "The kore-in-k corpus"); exit 77
# when they are absent. Under a 12 GiB memory scope. Usage: test/oracle-kore-in-k.sh  (`kcore` built first)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
[ -d .lake/kore-in-k ] || { echo "texts not built"; exit 77; }
cases=.lake/oracle-kore-in-k.jsonl; out=.lake/oracle-kore-in-k.txt
grep -E '"id": "(c03-nondet|c08-undef-rhs-blocks|c24-map-fn-pattern)/haskell"' kk/agree-kore-in-k.jsonl > "$cases"
# the definitions (`../.lake/kore-in-k/...`) resolve against the case file's directory, .lake as test/
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 600 \
  .lake/build/bin/kcore oracle "$cases" > "$out" 2>&1
got=$(python3 -I - "$out" <<'PY'
import json, sys
for line in open(sys.argv[1]):
    j = json.loads(line)
    print(j['id'], f"oracle:{str(j['oracle']).lower()}", f"reached:{j.get('reached', '-')}",
          f"N:{len(j.get('N', []))}", f"U:{len(j.get('U', []))}", f"coherent:{j.get('coherent', '-')}",
          f"vs:{j.get('vs_expected', '-')}")
PY
)
if diff <(sed -e '/^#/d' test/oracle-kore-in-k.expected) <(echo "$got"); then
  echo "oracle-kore-in-k: as expected (details in $out)"
else echo "oracle-kore-in-k: changed (above; details in $out)"; exit 1; fi
