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
# Usage: test/imp-tie.sh   (from anywhere)
set -u
K=$(cd "$(dirname "$0")/.." && pwd); cd "$K"
python3 -I - <<'EOF'
import re, sys, tomllib
rec = tomllib.load(open("test/imp-tie.toml", "rb"))
bad = []
def text(f):
    try: return open(f).read()
    except OSError: bad.append(f"{f}: cannot be read"); return ""
def stated(f, names):
    t = text(f)
    for n in names:
        if not re.search(r"^(theorem|kernel_rfl) " + re.escape(n) + r"\b", t, re.M):
            bad.append(f"{f}: no theorem {n}")
tie = text("test/TieKimp.lean")
m = re.search(r"theorem account_sizes : .*?=\s*\[(.*?)\] := by", tie, re.S)
sizes = [(a, int(b)) for a, b in re.findall(r'\("([^"]+)",\s*(\d+)\)', m.group(1))] if m else []
if not sizes: bad.append("test/TieKimp.lean: no account_sizes")
m = re.search(r"theorem userAxioms_length : U\.all\.length = (\d+)", tie)
if not m or int(m.group(1)) != rec["sentences"]: bad.append("userAxioms_length is not the record's sentences")
m = re.search(r"def tieClasses : List \(String × TieDir\) :=\s*\[(.*?)\]\n", text("KcoreSpec/TieDefs.lean"), re.S)
dirs = re.findall(r'\("([^"]+)",\s*\.(\w+)\)', m.group(1)) if m else []
classes = rec["class"]
m = re.search(r"def classes : List \(String × List Nat\) :=(.*?)\n\n", tie, re.S)
lists = {a: [int(x) for x in re.findall(r"\d+", b)] for a, b in re.findall(r'\("([^"]+)",\s*\[([^\]]*)\]\)', m.group(1))} if m else {}
if not lists: bad.append("test/TieKimp.lean: no classes")
def indices(f, names):
    t, out = text(f), []
    for n in names:
        m = re.search(r"^theorem " + re.escape(n) + r"\b.*?=\s*\[([\d,\s]*)\] :=", t, re.M | re.S)
        if not m: bad.append(f"{f}: no list stated by {n}"); continue
        out += [int(x) for x in re.findall(r"\d+", m.group(1))]
    return out
if [(c["name"], c["count"]) for c in classes] != sizes:
    bad.append(f"classes and counts differ from account_sizes: {sizes}")
if [(c["name"], c["direction"]) for c in classes] != dirs:
    bad.append(f"directions differ from tieClasses: {dirs}")
if sum(c["count"] for c in classes) != rec["sentences"]: bad.append("the counts do not sum to sentences")
tot = {k: 0 for k in ("proved", "at_values", "refuted", "no_direction", "remainder")}
for c in classes:
    parts = {k: c.get(k, 0) for k in tot}
    if sum(parts.values()) != c["count"]: bad.append(f"{c['name']}: the parts do not sum to the count")
    if parts["remainder"] and not c.get("reason"): bad.append(f"{c['name']}: a remainder without a reason")
    if c.get("theorems"): stated(c["file"], c["theorems"])
    if c.get("indices"):
        tied, rest = indices(c["file"], c["indices"]), c.get("remainder_indices", [])
        if len(tied) != parts["at_values"] + parts["refuted"]: bad.append(f"{c['name']}: {len(tied)} tied, not at_values + refuted")
        if len(rest) != parts["remainder"]: bad.append(f"{c['name']}: remainder_indices are not the remainder")
        if sorted(tied + rest) != sorted(lists.get(c["name"], [])): bad.append(f"{c['name']}: tied and remainder_indices do not partition the class")
    for k in tot: tot[k] += parts[k]
l1 = rec["layer1"]
stated(l1["file"], l1["theorems"]); stated(l1["wf_file"], l1["wf_theorems"]); stated(l1["sig_file"], l1["sig_theorems"])
stated(rec["declarations"]["file"], rec["declarations"]["theorems"])
stated(rec["consistent"]["file"], rec["consistent"]["theorems"])
stated(rec["consistent"]["reach_file"], rec["consistent"]["reach_theorems"])
if not re.search(r"\bconsistent\b", text(rec["consistent"]["pinned"])): bad.append("consistent is not pinned")
if bad:
    print("\n".join("imp-tie: " + b for b in bad)); sys.exit(1)
print(f"imp-tie: {rec['sentences']} sentences: " + ", ".join(f"{k.replace('_', ' ')} {v}" for k, v in tot.items()))
EOF
