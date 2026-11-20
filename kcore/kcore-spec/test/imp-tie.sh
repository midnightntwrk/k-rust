#!/usr/bin/env bash
# Row imp, tied (DONE-0 C14 part 3): test/imp-tie.toml records, per class of the account of kimp's
# user module, the count and how many sentences are kernel-checked on kimp's text in the class's
# direction, at values, refuted or without direction, and the remainder with its reason. This
# script checks the record by text, without Lean, against the files it names:
#   - the classes, in order, with their counts, are those `account_sizes` states in
#     test/TieKimp.lean, and their sum is the record's `sentences` and `userAxioms_length`'s;
#   - each class's direction is the one `tieClasses` gives it (KcoreSpec/TieDefs.lean);
#   - per class, proved + at_values + refuted + no_direction + remainder = count, and a class with
#     a remainder gives its reason;
#   - every theorem the record names is stated (`theorem NAME`) in the file it names;
#   - where a class names `indices`, the lists those theorems state (`theorem NAME : … = [list]`)
#     hold its tied sentences: their number is the class's at_values + refuted, and with its
#     `remainder_indices` (as many as its remainder) they partition the class's list in `classes`
#     of test/TieKimp.lean.
# That the theorems check is their files' run (each is a test file, or the package's module);
# this script reads none of them as Lean.
# The same checks read another row's record given as RECORD (test/kk-tie.sh: test/kk-tie.toml): the
# account's file is the record's [layer1] file, a theorem or an index list written FILE::NAME is
# looked up in FILE, every FOO_file of [layer1] is checked with its FOO_theorems, and a class may
# count sentences tied under a named condition on H (`hypothesis`, its `condition` given).
# Usage: test/imp-tie.sh [RECORD]   (from anywhere; RECORD kcore-spec-relative, test/imp-tie.toml by default)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
python3 -I - "${1:-test/imp-tie.toml}" <<'EOF'
import re, sys, tomllib
recf = sys.argv[1]
tag = recf.rsplit("/", 1)[-1].removesuffix(".toml")
rec = tomllib.load(open(recf, "rb"))
bad = []
def text(f):
    try: return open(f).read()
    except OSError: bad.append(f"{f}: cannot be read"); return ""
def split(f, n):
    return tuple(n.split("::", 1)) if "::" in n else (f, n)
def stated(f, names):
    for n in names:
        g, n = split(f, n)
        if not re.search(r"^(theorem|kernel_rfl) " + re.escape(n) + r"\b", text(g), re.M):
            bad.append(f"{g}: no theorem {n}")
acc = rec["layer1"]["file"]
tie = text(acc)
m = re.search(r"theorem account_sizes : .*?=\s*\[(.*?)\] := by", tie, re.S)
sizes = [(a, int(b)) for a, b in re.findall(r'\("([^"]+)",\s*(\d+)\)', m.group(1))] if m else []
if not sizes: bad.append(f"{acc}: no account_sizes")
m = re.search(r"theorem userAxioms_length : U\.all\.length = (\d+)", tie)
if not m or int(m.group(1)) != rec["sentences"]: bad.append("userAxioms_length is not the record's sentences")
m = re.search(r"def tieClasses : List \(String × TieDir\) :=\s*\[(.*?)\]\n", text("KcoreSpec/TieDefs.lean"), re.S)
dirs = re.findall(r'\("([^"]+)",\s*\.(\w+)\)', m.group(1)) if m else []
classes = rec["class"]
m = re.search(r"def classes : List \(String × List Nat\) :=(.*?)\n\n", tie, re.S)
lists = {a: [int(x) for x in re.findall(r"\d+", b)] for a, b in re.findall(r'\("([^"]+)",\s*\[([^\]]*)\]\)', m.group(1))} if m else {}
if not lists: bad.append(f"{acc}: no classes")
def indices(f, names):
    out = []
    for n in names:
        g, n = split(f, n)
        m = re.search(r"^theorem " + re.escape(n) + r"\b.*?=\s*\[([\d,\s]*)\] :=", text(g), re.M | re.S)
        if not m: bad.append(f"{g}: no list stated by {n}"); continue
        out += [int(x) for x in re.findall(r"\d+", m.group(1))]
    return out
if [(c["name"], c["count"]) for c in classes] != sizes:
    bad.append(f"classes and counts differ from account_sizes: {sizes}")
if [(c["name"], c["direction"]) for c in classes] != dirs:
    bad.append(f"directions differ from tieClasses: {dirs}")
if sum(c["count"] for c in classes) != rec["sentences"]: bad.append("the counts do not sum to sentences")
tot = {k: 0 for k in ("proved", "at_values", "hypothesis", "refuted", "no_direction", "remainder")}
for c in classes:
    parts = {k: c.get(k, 0) for k in tot}
    if sum(parts.values()) != c["count"]: bad.append(f"{c['name']}: the parts do not sum to the count")
    if parts["remainder"] and not c.get("reason"): bad.append(f"{c['name']}: a remainder without a reason")
    if parts["hypothesis"] and not c.get("condition"): bad.append(f"{c['name']}: a hypothesis without its condition")
    if c.get("theorems"): stated(c["file"], c["theorems"])
    if c.get("indices"):
        tied, rest = indices(c["file"], c["indices"]), c.get("remainder_indices", [])
        if len(tied) != parts["at_values"] + parts["hypothesis"] + parts["refuted"]:
            bad.append(f"{c['name']}: {len(tied)} tied, not at_values + hypothesis + refuted")
        if len(rest) != parts["remainder"]: bad.append(f"{c['name']}: remainder_indices are not the remainder")
        if sorted(tied + rest) != sorted(lists.get(c["name"], [])): bad.append(f"{c['name']}: tied and remainder_indices do not partition the class")
    for k in tot: tot[k] += parts[k]
l1 = rec["layer1"]
stated(l1["file"], l1["theorems"])
for k in l1:
    if k.endswith("_file"): stated(l1[k], l1.get(k[:-5] + "_theorems", []))
stated(rec["declarations"]["file"], rec["declarations"]["theorems"])
stated(rec["consistent"]["file"], rec["consistent"]["theorems"])
if "reach_file" in rec["consistent"]: stated(rec["consistent"]["reach_file"], rec["consistent"]["reach_theorems"])
if not re.search(r"\bconsistent\b", text(rec["consistent"]["pinned"])): bad.append("consistent is not pinned")
if bad:
    print("\n".join(f"{tag}: " + b for b in bad)); sys.exit(1)
print(f"{tag}: {rec['sentences']} sentences: " + ", ".join(f"{k.replace('_', ' ')} {v}" for k, v in tot.items()))
EOF
