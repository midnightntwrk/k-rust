#!/usr/bin/env bash
# Agreement with the reference backends' cached results: `kcore agree` over test/agree.jsonl (built
# by test/agree-cases.py from the reference cache; its definitions are read from the corpus
# extraction, so test/corpus.py runs first), one line per case `VERDICT ID` (with `by:CExec` or
# `by:Exec`, the executable step whose result an `agree` or `differ` compares, and `anyway:VERDICT`
# where the case was run outside what the executable steps cover), compared with
# test/agree.expected, where `#` starts a comment (a line's reason for its verdict). Under a 12 GiB
# memory scope. Details (reasons, both results of a `differ`, a search's undefined-result
# configurations) in .lake/NAME.txt. Usage: test/agree.sh [CASES.jsonl EXPECTED]  (`kcore` built first; by default
# test/agree.jsonl and test/agree.expected; NAME is the case file's name without .jsonl)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
cases=${1:-test/agree.jsonl}; expected=${2:-test/agree.expected}
name=$(basename "$cases" .jsonl)
out=.lake/$name.txt; verdicts=.lake/$name.verdicts
systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0 timeout 1800 \
  .lake/build/bin/kcore agree "$cases" > "$out" 2>&1
python3 -I - "$out" > "$verdicts" <<'PY'
import json, re, sys
for line in open(sys.argv[1]):
    j = json.loads(line)
    if 'note' in j:
        print(j['note'], file=sys.stderr)
    if 'id' not in j:
        continue
    m = re.search(r'run anyway with \S+: (\S+)', j['reason'])
    by = ['by:' + j['executable']] if j.get('executable') else []
    print(j['verdict'], j['id'], *by, *(['anyway:' + m.group(1)] if m else []))
PY
counts=$(cut -d' ' -f1 "$verdicts" | sort | uniq -c | tr -s ' ' | tr '\n' ',' | sed 's/,$//')
if diff <(sed -e '/^#/d' -e 's/ *#.*$//' "$expected") "$verdicts"; then
  echo "$name:$counts (as expected; details in $out)"
else echo "$name: verdicts changed (above;$counts; details in $out)"; exit 1; fi
