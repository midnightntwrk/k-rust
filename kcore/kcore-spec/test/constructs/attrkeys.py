"""The reader's attribute keys against the construct table (DONE-0 C4 part 2).

Usage (from kcore-spec): python3 -I test/constructs/attrkeys.py OUT [ROWS.toml]
  OUT  what `lake env lean test/AttrVerdict.lean` prints: a line `row CLASS NAME STATUS` per row
       of its list rowsE2, and a line `key NAME KORE-SPELLING` per constructor of Parse.AttrKeyE2
       (KcoreSpec/ParseAttr.lean).
Fails (exit 1) unless
  - the `row` lines are exactly E2's rows of a class other than frontend, `NAME(name)@class`, each
    with the row's status: the list the kernel checks Parse.attrVerdict against is the table's;
  - the `key` names are exactly the names of those rows, each once.
Prints the counts, and every attribute name at the head of an attribute of a sentence of a
fixture's kore.txt that is no key's KORE spelling, with how many sentences carry it and one fixture:
a name the frontend writes that E2 does not list (it is no key of K's attribute table).
"""
import collections, os, re, sys, tomllib

K = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
out = sys.argv[1]
rows = sys.argv[2] if len(sys.argv) > 2 else os.path.join(K, "test/constructs/rows.toml")
FX = os.path.join(K, "test/constructs/fixtures")


def attr_heads(line):
    """The heads of the attribute list that ends a KORE sentence written on one line."""
    s = line.rstrip()
    m = re.search(r"\]\s*(//.*)?$", s)
    if not m:
        return []
    end, depth, instr, j = m.start(), 0, False, m.start()
    while j >= 0:                      # back to the bracket that opens the list
        ch = s[j]
        if ch == '"':
            b, k = 0, j - 1
            while k >= 0 and s[k] == "\\":
                b, k = b + 1, k - 1
            if b % 2 == 0:
                instr = not instr
        elif not instr:
            if ch == "]":
                depth += 1
            elif ch == "[":
                depth -= 1
                if depth == 0:
                    break
        j -= 1
    if j < 0:
        return []
    body, heads, depth, instr, cur, k = s[j + 1:end], [], 0, False, "", 0
    while k < len(body):
        ch = body[k]
        if instr:
            if ch == "\\":
                k += 1
            elif ch == '"':
                instr = False
        elif ch == '"':
            instr = True
        elif ch in "({[":
            if depth == 0 and ch == "{":
                heads.append(cur.strip())
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif ch == "," and depth == 0:
            cur, k = "", k + 1
            continue
        if depth == 0 and not instr and ch not in ")}]":
            cur += ch
        k += 1
    return [h for h in heads if h]


t = tomllib.load(open(rows, "rb"))["E2"]
table = {}
for key, r in t.items():
    m = re.match(r"[A-Z_0-9]+\(([^)]*)\)@(\w+)$", key)
    if m and m[2] != "frontend":
        table[(m[2], m[1])] = r.get("status")
lean, keys = {}, []
for line in open(out):
    w = line.split()
    if len(w) == 4 and w[0] == "row":
        lean[(w[1], w[2])] = w[3]
    elif len(w) == 3 and w[0] == "key":
        keys.append((w[1], w[2]))
bad = []
for p in sorted(set(table) | set(lean)):
    if table.get(p) != lean.get(p):
        bad.append(f"{p[1]}@{p[0]}: rows.toml {table.get(p, 'no row')}, test/AttrVerdict.lean {lean.get(p, 'no row')}")
names = [n for n, _ in keys]
rownames = {n for _, n in table}
for n in sorted(rownames - set(names)):
    bad.append(f"{n}: a name of E2's rows that is no key of AttrKeyE2")
for n in sorted(set(names) - rownames):
    bad.append(f"{n}: a key of AttrKeyE2 that is no name of E2's rows")
for n in sorted({n for n in names if names.count(n) > 1}):
    bad.append(f"{n}: a key of AttrKeyE2 twice")
spell = {s for _, s in keys}
seen, where = collections.Counter(), {}
for d in sorted(os.listdir(FX)):
    p = os.path.join(FX, d, "kore.txt")
    if os.path.isfile(p):
        for line in open(p):
            for h in attr_heads(line):
                if h not in spell:
                    seen[h] += 1
                    where.setdefault(h, d)
print(f"attrkeys: {len(lean)} rows of E2 reach KORE, {len(set(names))} keys of AttrKeyE2 over {len(table)} rows of the table"
      f"; attribute names of the fixtures' kore.txt that are no key: {len(seen)}"
      + "".join(f"; {h} ({seen[h]} sentences, e.g. {where[h]})" for h in sorted(seen)))
for b in bad[:20]:
    print(f"  FAILS: {b}")
sys.exit(1 if bad else 0)
