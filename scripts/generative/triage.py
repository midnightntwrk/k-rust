#!/usr/bin/env python3
"""Triage the results of the generative compile test.

Usage: triage.py RESULTS.tsv CORPUS_DIR [--expected FILE] [--list ID|unexpected]

RESULTS.tsv is the output of `generative-compile run`. Every row is one of:
  pass        compiled, and the emitted KORE loaded in the Rust backend
  expected    rejected with an ordinary error that a category of expected.toml (next to this
              script, or --expected FILE) explains as invalid input
  unexpected  an oracle violation (panic, crash, timeout, KORE parse error, backend failure after
              a successful compilation), an error located in a builtin source, or an ordinary
              error that no category explains

Prints a summary and exits 1 when any row is unexpected, 0 otherwise. `--list ID` prints the rows
of one category, `--list unexpected` the unexpected rows.
"""
import os
import re
import sys
import tomllib
from collections import Counter, defaultdict

# Outcomes for which an expected category may apply; every other non-pass outcome is a violation.
ORDINARY_ERRORS = {"load_error", "parse_error", "compile_error"}
# The prelude loads and compiles on its own, so an error that points into it does not blame the
# case's text: the case changed how builtin text is read, or the error is misattributed.
BUILTIN_SOURCE = "krust-builtin://"


def usage():
    print(__doc__.strip().splitlines()[2], file=sys.stderr)
    sys.exit(2)


def load_categories(path):
    with open(path, "rb") as fh:
        data = tomllib.load(fh)
    categories = []
    for entry in data.get("category", []):
        missing = {"id", "outcome", "message", "reason"} - entry.keys()
        if missing:
            sys.exit(f"{path}: category {entry.get('id', '?')} lacks {sorted(missing)}")
        categories.append({
            "id": entry["id"],
            "outcome": re.compile(entry["outcome"]),
            "message": re.compile(entry["message"]),
            "source": re.compile(entry["source"]) if "source" in entry else None,
            "internal": entry.get("internal", False),
            "reason": entry["reason"],
        })
    ids = [c["id"] for c in categories]
    duplicates = sorted({i for i in ids if ids.count(i) > 1})
    if duplicates:
        sys.exit(f"{path}: duplicate category ids {duplicates}")
    return categories


def classify(row, corpus, categories):
    """Return (verdict, key): verdict is pass, expected, or unexpected; key is the category id
    for an expected row and the reason for an unexpected one."""
    outcome, message = row["outcome"], row["first_line"]
    if outcome == "pass":
        return "pass", None
    if outcome not in ORDINARY_ERRORS:
        return "unexpected", "oracle violation"
    if BUILTIN_SOURCE in message:
        return "unexpected", "error located in a builtin source"
    text = None
    for category in categories:
        if not (category["outcome"].search(outcome) and category["message"].search(message)):
            continue
        if category["source"] is not None:
            if text is None:
                with open(os.path.join(corpus, row["file"])) as fh:
                    text = fh.read()
            if not category["source"].search(text):
                continue
        return "expected", category["id"]
    return "unexpected", "no category"


def group_key(row):
    """Collapse generated names and numbers so that rows with one cause group together."""
    message = re.sub(r"'Lbl\S*':", "'Lbl...':", row["first_line"])
    message = re.sub(r"\d+", "N", message)
    return f"{row['outcome']}: {message[:160]}"


def main():
    args = sys.argv[1:]
    if len(args) < 2:
        usage()
    results, corpus = args[0], args[1]
    expected_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "expected.toml")
    show = None
    rest = args[2:]
    while rest:
        option = rest.pop(0)
        if option == "--expected" and rest:
            expected_path = rest.pop(0)
        elif option == "--list" and rest:
            show = rest.pop(0)
        else:
            usage()
    categories = load_categories(expected_path)
    with open(results) as fh:
        header = fh.readline().rstrip("\n").split("\t")
        rows = [dict(zip(header, line.rstrip("\n").split("\t"))) for line in fh if line.strip()]

    by_category = defaultdict(list)
    unexpected = defaultdict(list)
    for row in rows:
        verdict, key = classify(row, corpus, categories)
        if verdict == "expected":
            by_category[key].append(row)
        elif verdict == "unexpected":
            row["why"] = key
            unexpected[group_key(row)].append(row)

    if show is not None:
        selected = ([r for group in unexpected.values() for r in group] if show == "unexpected"
                    else by_category.get(show, []))
        for row in selected:
            print("\t".join([row["file"], row["outcome"], row["location"], row["first_line"]]))
        return 0

    outcomes = Counter(row["outcome"] for row in rows)
    print(f"{len(rows)} cases: " + ", ".join(f"{k} {v}" for k, v in outcomes.most_common()))
    n_expected = sum(len(v) for v in by_category.values())
    n_unexpected = sum(len(v) for v in unexpected.values())
    print(f"pass {outcomes.get('pass', 0)}, expected rejections {n_expected}, unexpected {n_unexpected}")
    print()
    print("Expected rejections (invalid input):")
    for category in categories:
        matched = by_category.get(category["id"])
        if not matched:
            continue
        located = sum(r["location"] == "loc" for r in matched)
        tag = " internal" if category["internal"] else ""
        print(f"  {len(matched):5d}  {category['id']:<36} loc {located}/{len(matched)}{tag}  e.g. {matched[0]['file']}")
    unused = [c["id"] for c in categories if c["id"] not in by_category]
    if unused:
        print(f"  (no rows: {', '.join(unused)})")
    print()
    if not unexpected:
        print("Unexpected: none")
        return 0
    print("Unexpected (compiler or harness defects until shown otherwise):")
    for key, group in sorted(unexpected.items(), key=lambda item: (-len(item[1]), item[0])):
        files = " ".join(r["file"] for r in group[:4]) + (" ..." if len(group) > 4 else "")
        print(f"  {len(group):5d}  [{group[0]['why']}] {key}")
        print(f"         {files}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
