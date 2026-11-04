#!/usr/bin/env python3
"""Collapse the exact diagnostic entries of krs/tests/class-matrix/pending.toml into family entries.

Usage: python3 -I scripts/krs-class-collapse-pending.py TSV_DIR [PENDING] > NEW_PENDING

TSV_DIR holds a whole run of every shard, `<shard>/<shard>.tsv` as `KRS_CLASS_OUT` writes it
(one verdict line per key, and a `red` line per pended red with its computed kind). PENDING
defaults to the checked-in file. The new file goes to stdout; a report per finding goes to stderr.

A family entry (`class_matrix::pending`) pends every red of one diagnostic kind whose key its glob
matches, under one finding. The script collapses, per finding, kind and shard, the exact entries of
the reds of a family kind into the fewest globs it finds that match exactly those keys among every
key the run made a verdict on, and every key of a case (`ID` and `k8/ID`): no glob reaches a case
that is green, a red of another finding or kind, or a red of another shard. No two globs match one
key. Entries it does not collapse stay exact, in place: reds of a meaning kind, `full/..` entries
and the `ID` entry of a case that has one (the two tiers observe it otherwise), and entries no red
line of the run names.

A glob is a sequence of `/`-separated segments, each a literal, `*`, or `{a,b,..}` of literals,
whose first segment is a literal (it names the key's test and family). Such a glob matches a key
exactly when the key has as many segments and each matches, which is how `Glob` reads it: `*`
does not cross `/`.

The proof that the new file pends what the old one did is `KRS_PENDING_PROOF_TSV=TSV_DIR
KRS_PENDING_PROOF_OLD=OLD cargo test -p krs-test-support --test class_matrix -- --ignored
the_collapsed_red_list_pends_what_the_exact_one_did`.
"""

import collections
import itertools
import os
import re
import sys
import tomllib

FAMILY_KINDS = {"diagnostic", "diagnostic+rust-syntax", "lint-missing", "lint-unowed", "k8"}
PREFIXES = ("k1/", "k3/", "k6/", "k7/", "twin/", "k8/", "full/", "lattice/", "entry/")
WILD = "*"
# The lines that open and close the family section.
FAMILIES = "# Family entries, by finding: each pends the reds of its kind whose key its glob matches"
EXACT = "# Exact entries, one per case, in place."
# Masks over more segments than this keep the later segments literal.
MASKED_SEGMENTS = 7


def test_of(key):
    for prefix in PREFIXES:
        if key.startswith(prefix):
            return prefix[:-1]
    return "k2"


def read_run(directory):
    verdicts, reds = {}, {}
    for shard in sorted(os.listdir(directory)):
        path = os.path.join(directory, shard, f"{shard}.tsv")
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as lines:
            for line in lines:
                fields = line.rstrip("\n").split("\t")
                if fields[0] == "red":
                    reds[fields[1]] = (shard, fields[2], fields[3])
                elif len(fields) == 3 and "/" in fields[0]:
                    verdicts[fields[0]] = (shard, fields[1], fields[2])
    return verdicts, reds


def literal(segment):
    return "".join("\\" + c if c in "\\*{}," else c for c in segment)


def glob_text(pattern):
    parts = []
    for item in pattern:
        if item == WILD:
            parts.append(WILD)
        elif len(item) == 1:
            parts.append(literal(next(iter(item))))
        else:
            parts.append("{" + ",".join(literal(text) for text in sorted(item)) + "}")
    return "/".join(parts)


def glob_regex(pattern):
    """The regular expression of a glob in `Glob`'s syntax: `*` within a segment, `{a,b}`."""
    out, depth, chars = [], 0, iter(pattern)
    for c in chars:
        if c == "\\":
            out.append(re.escape(next(chars)))
        elif c == "*":
            out.append("[^/]*")
        elif c == "{":
            out.append("(?:")
            depth += 1
        elif c == "}" and depth:
            out.append(")")
            depth -= 1
        elif c == "," and depth:
            out.append("|")
        else:
            out.append(re.escape(c))
    return re.compile("".join(out) + r"\Z")


def toml_string(text):
    if "'" not in text and "\n" not in text:
        return f"'{text}'"
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def collapse(group, universe, fixed):
    """The fewest disjoint product globs it finds whose match among `universe` is `group`."""
    by_length = collections.defaultdict(list)
    for key in universe:
        by_length[len(key.split("/"))].append(key)
    index = {}

    def matching(length, mask, projection):
        if (length, mask) not in index:
            table = collections.defaultdict(list)
            for key in by_length[length]:
                segments = key.split("/")
                table[tuple(s for i, s in enumerate(segments) if i not in mask)].append(key)
            index[(length, mask)] = table
        return index[(length, mask)].get(projection, [])

    candidates = {}
    for key in group:
        segments = key.split("/")
        free = list(range(fixed, min(len(segments), fixed + MASKED_SEGMENTS)))
        for size in range(len(free) + 1):
            for mask in itertools.combinations(free, size):
                mask = frozenset(mask)
                projection = tuple(s for i, s in enumerate(segments) if i not in mask)
                pattern = tuple(
                    WILD if i in mask else frozenset([s]) for i, s in enumerate(segments)
                )
                if pattern in candidates:
                    continue
                covered = matching(len(segments), mask, projection)
                if all(other in group for other in covered):
                    candidates[pattern] = frozenset(covered)
    ordered = sorted(
        candidates.items(),
        key=lambda item: (-len(item[1]), sum(p == WILD for p in item[0]), glob_text(item[0])),
    )
    chosen, covered = [], set()
    for pattern, keys in ordered:
        if keys and not keys & covered:
            chosen.append((pattern, keys))
            covered |= keys
    assert covered == group, "every key is its own candidate"
    # Merge two products that differ at one literal position: their union is the product of the
    # union there, and stays disjoint from the others.
    merged = True
    while merged:
        merged = False
        for (a, keys_a), (b, keys_b) in itertools.combinations(chosen, 2):
            differ = [i for i in range(len(a)) if len(a) == len(b) and a[i] != b[i]]
            if (
                len(a) == len(b)
                and len(differ) == 1
                and differ[0] >= fixed
                and a[differ[0]] != WILD
                and b[differ[0]] != WILD
            ):
                i = differ[0]
                union = a[:i] + (a[i] | b[i],) + a[i + 1 :]
                chosen.remove((a, keys_a))
                chosen.remove((b, keys_b))
                chosen.append((union, keys_a | keys_b))
                merged = True
                break
    return sorted((glob_text(pattern), keys) for pattern, keys in chosen)


def main():
    directory = sys.argv[1]
    pending_path = (
        sys.argv[2]
        if len(sys.argv) > 2
        else os.path.join(os.path.dirname(__file__), "../krs/tests/class-matrix/pending.toml")
    )
    with open(pending_path, "rb") as file:
        pending = tomllib.load(file)
    with open(pending_path, encoding="utf-8") as file:
        text = file.read()
    verdicts, reds = read_run(directory)
    exact = {key: entry for key, entry in pending.items() if key != "family"}
    kept = [
        (family["finding"], family["kind"], family["match"], glob_regex(family["match"]))
        for family in pending.get("family", [])
    ]

    def kept_family(key):
        return next((family for family in kept if family[3].match(key)), None)

    ids = set()
    for key in verdicts:
        if test_of(key) == "k2":
            ids.add(key)
        elif key.startswith("full/"):
            ids.add(key[len("full/") :])
    universe = {
        "k2": ids,
        "k8": {f"k8/{case}" for case in ids} | {k for k in verdicts if k.startswith("k8/")},
    }
    groups = collections.defaultdict(set)
    for key, (shard, kind, finding) in reds.items():
        test = test_of(key)
        if (
            kind in FAMILY_KINDS
            and test in universe
            and key in exact
            and exact[key]["finding"] == finding
            and f"full/{key}" not in exact
            and key in universe[test]
            and kept_family(key) is None
        ):
            groups[(finding, kind, shard, test)].add(key)

    families, removed = [], set()
    for family in kept:
        held = [k for k in reds if k not in exact and family[3].match(k)]
        shard = ", ".join(sorted({reds[k][0] for k in held})) or "no red"
        families.append((family[0], family[1], shard, family[2], len(held)))
    for (finding, kind, shard, test), group in sorted(groups.items()):
        fixed = 2 if test == "k8" else 1
        for glob, keys in collapse(group, universe[test], fixed):
            families.append((finding, kind, shard, glob, len(keys)))
        removed |= group
    families.sort(key=lambda row: (row[0], row[1], row[2], row[3]))

    before = collections.Counter(entry["finding"] for entry in exact.values())
    after = collections.Counter(
        entry["finding"] for key, entry in exact.items() if key not in removed
    )
    before.update(finding for finding, *_ in kept)
    family_count = collections.Counter(finding for finding, *_ in families)
    print("finding\tentries before\texact after\tfamilies after\tcollapsed", file=sys.stderr)
    for finding in sorted(before):
        print(
            f"{finding}\t{before[finding]}\t{after[finding]}\t{family_count[finding]}\t"
            f"{before[finding] - after[finding]}",
            file=sys.stderr,
        )
    print(
        f"total\t{sum(before.values())}\t{sum(after.values())}\t{len(families)}\t{len(removed)}",
        file=sys.stderr,
    )

    # The file: its header (the comment up to the first blank line), the family section (between
    # FAMILIES and EXACT, regenerated), then the exact entries left, each in place.
    lines = text.split("\n")
    header_end = lines.index("")
    header, body = lines[:header_end], lines[header_end:]
    if FAMILIES in body:
        start, end = body.index(FAMILIES), body.index(EXACT)
        body = body[:start] + body[end + 1 :]
    exact_lines, skipping = [], False
    for line in body:
        if line.startswith('["') and line.endswith('"]'):
            key = tomllib.loads("k = " + line[1:-1])["k"]
            skipping = key in removed
        elif not line:
            if skipping:
                skipping = False
                continue
        if not skipping:
            exact_lines.append(line)
    out = list(header) + ["", FAMILIES]
    out.append("# (see the header); the count is the reds each pended when")
    out.append("# scripts/krs-class-collapse-pending.py last wrote this section.")
    out.append("")
    for (finding, kind), rows in itertools.groupby(families, key=lambda row: (row[0], row[1])):
        rows = list(rows)
        out.append(f"# {finding}, {kind}: {sum(row[4] for row in rows)} reds")
        out.append("")
        for _, _, shard, glob, count in rows:
            out.append(f"# {shard}: {count}")
            out.append("[[family]]")
            out.append(f"match = {toml_string(glob)}")
            out.append(f'finding = "{finding}"')
            out.append(f'kind = "{kind}"')
            out.append("")
    out.append(EXACT)
    out.extend(exact_lines)
    result = "\n".join(out)
    while "\n\n\n" in result:
        result = result.replace("\n\n\n", "\n\n")
    sys.stdout.write(result if result.endswith("\n") else result + "\n")


if __name__ == "__main__":
    main()
