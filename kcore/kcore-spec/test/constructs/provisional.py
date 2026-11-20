"""The status rows of core-manifest.toml against the construct table (DONE-0 C5 part 4).

Every table of the manifest is read, the inline tables of its arrays (a layer's `except`) among
them. Fails on:
- an entry with status = "provisional", outside the allowance;
- an entry with `relabelled` (stable though what it describes is not resolved: the field says why)
  whose status is not "stable", or whose `leaves` is neither the sentence
  "no construct depends on it" nor a non-empty list of references "<list> <row key>[, case <name>]"
  to entries of ROWS.toml whose status is refused or parameter (for a case, the `cases` entry of the
  row whose `case` is <name>, its own status, or the row's when it has none);
- an entry with `leaves` and no `relabelled`;
- an entry whose `rows` (the rows.toml entries it names, of any status) is not a list of references
  "<list> <row key>[, case <name>]" to entries of ROWS.toml.
The sentence is checked here for its presence only; whether it is true is the gate's to judge.

The allowance (ALLOWANCE below): a provisional entry, named by its declaration, that a pending ticket
of PROGRESS owes, as units.py's and closed.py's allowances are owed. It holds only while the entry is
provisional, its `ticket` field names the ticket, and the ticket is in PROGRESS with a status other
than done; an allowance whose entry is missing or no longer provisional, or whose ticket is missing
or done, fails. Every run prints each allowance. DONE-0 C5 part 4 is not met while one is listed.
  PROGRESS  as units.py: KCORE_PROGRESS, else ../progress, else the main checkout's.

Usage (from kcore-spec): python3 -I test/constructs/provisional.py [MANIFEST [ROWS.toml]]
  MANIFEST   default ../core-manifest.toml
  ROWS.toml  default test/constructs/rows.toml
Prints each relabelled entry with what it leaves, then each failure. Exit 1 on a failure."""
import glob, os, re, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
man = sys.argv[1] if len(sys.argv) > 1 else os.path.join(K, "../core-manifest.toml")
rows = sys.argv[2] if len(sys.argv) > 2 else os.path.join(K, "test/constructs/rows.toml")
SENTENCE = "no construct depends on it"
ROWREF = re.compile(r"(E[1-8]) (.+?)(?:, case (.+))?$", re.S)
LEFT = {"refused", "parameter"}

m = tomllib.load(open(man, "rb"))
t = tomllib.load(open(rows, "rb"))
KR = os.environ.get("K_RUST", os.path.expanduser(
    "~/git/workspaces/starstream-fv/inspirations/midnightntwrk/k-rust"))
prog = os.environ.get("KCORE_PROGRESS") or next(
    (d for d in (os.path.join(K, "../progress"),
                 os.path.join(KR, "draft-personal/k-semantics-core-2026-11/progress"))
     if os.path.isdir(d)), os.path.join(K, "../progress"))

# Provisional entries owed by a ticket of PROGRESS: (the entry's declaration, ticket). None is owed.
ALLOWANCE = []


def entries(v, where):
    """Every table in v, with a name for it."""
    if isinstance(v, dict):
        yield where, v
        for k, x in v.items():
            yield from entries(x, f"{where}.{k}" if where else k)
    elif isinstance(v, list):
        for i, x in enumerate(v):
            yield from entries(x, f"{where}[{i}]")


def name(where, e):
    """The entry's place, with its id or declaration when it has one."""
    tag = e.get("id") or e.get("declaration")
    return f"{where} ({str(tag)[:60]!r})" if tag else where


def status_of(ref):
    """(status, None) of the entry ref names, or (None, why not)."""
    r = ROWREF.match(ref) if isinstance(ref, str) else None
    if not r:
        return None, f"{ref!r} is not \"<list> <row key>[, case <name>]\""
    row = t.get(r[1], {}).get(r[2])
    if not isinstance(row, dict):
        return None, f"{r[2]!r} is no key of {r[1]}"
    if r[3] is None:
        return row.get("status"), None
    cs = row.get("cases")
    cs = cs if isinstance(cs, list) else [cs]
    hit = [c for c in cs if isinstance(c, dict) and str(c.get("case")) == r[3]]
    if len(hit) != 1:
        return None, f"{r[1]} {r[2]!r} has {len(hit)} cases named {r[3]!r}, not one"
    return hit[0].get("status", row.get("status")), None


tstatus = {}
for f in sorted(glob.glob(os.path.join(prog, "tickets-*.toml"))):
    for tid, tk in tomllib.load(open(f, "rb")).get("ticket", {}).items():
        tstatus[tid] = tk.get("status")
allowed = dict(ALLOWANCE)
seen = set()

bad, shown = [], 0
if not tstatus:
    bad.append(f"no progress/tickets-*.toml under {prog} (set KCORE_PROGRESS)")
for where, e in entries(m, ""):
    n = name(where, e)
    if e.get("status") == "provisional":
        d = e.get("declaration")
        tid = allowed.get(d)
        if tid is None:
            bad.append(f"{n}: status provisional")
        else:
            seen.add(d)
            st = tstatus.get(tid)
            why = ("" if st not in (None, "done") and tid in str(e.get("ticket", "")) else
                   f"its ticket field does not name {tid}" if st not in (None, "done") else
                   f"ticket {tid} is not in {prog}/tickets-*.toml" if st is None else
                   f"ticket {tid} is done, so it owes nothing")
            print(f"allowance {n}: provisional, owed by {tid} (status {st})")
            if why:
                bad.append(f"{n}: allowance: {why}")
    if "rows" in e:
        rs = e["rows"]
        if not isinstance(rs, list) or not rs:
            bad.append(f"{n}: rows is not a list of rows.toml keys")
        else:
            bad += [f"{n}: rows {why}" for why in (status_of(r)[1] for r in rs) if why]
    if "relabelled" not in e:
        if "leaves" in e:
            bad.append(f"{n}: leaves without relabelled")
        continue
    if not isinstance(e["relabelled"], str) or not e["relabelled"].strip():
        bad.append(f"{n}: relabelled is not a reason")
    if e.get("status") != "stable":
        bad.append(f"{n}: relabelled, status {e.get('status')!r}, not stable")
    lv = e.get("leaves")
    if lv == SENTENCE:
        print(f"relabelled {n}: {SENTENCE}")
        shown += 1
        continue
    if not isinstance(lv, list) or not lv:
        bad.append(f"{n}: relabelled, leaves is neither {SENTENCE!r} nor a list of rows.toml keys")
        continue
    nb = len(bad)
    for ref in lv:
        s, why = status_of(ref)
        if why:
            bad.append(f"{n}: leaves {why}")
        elif s not in LEFT:
            bad.append(f"{n}: leaves {ref!r}, of status {s!r}, neither refused nor parameter")
    if len(bad) == nb:
        print(f"relabelled {n}: leaves {len(lv)} rows.toml entries refused or parameter")
    shown += 1

for d, tid in ALLOWANCE:
    if d not in seen:
        bad.append(f"allowance {d[:60]!r} ({tid}): no provisional entry has this declaration; remove it")

print(f"provisional: {shown} relabelled entries; {len(seen)} allowed provisional; {len(bad)} failures")
for b in bad:
    print(f"  {b}")
sys.exit(1 if bad else 0)
