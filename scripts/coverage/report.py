"""Coverage tables from the exports of scripts/coverage.sh.

usage: report.py WORK GRAPH_TOML SUITE...

Reads WORK/export/SUITE.pickle (collect.py) for each suite and the algorithm graph that
`algo-graph graph` wrote, and writes WORK/report/:

- summary.md: totals per suite and per crate, and the problems collect.py reported;
- files.md: files of at least 150 production lines, most unexecuted lines first;
- cards.md and cards.json: for each algorithm card, how many lines of its sites each suite
  executed, and, for a suite collected per test, which tests execute a site;
- tests.tsv: for each test of a suite collected per test, the production lines it executed and
  how many of them no other test of that suite executed;
- uncovered.txt: the production lines no suite executed, as file:first-last ranges;
- totals.json: the numbers behind summary.md.

A line counts when llvm-cov reports it for some binary that was built for these suites; the
denominator is the union over all of them. Test code (files under tests/, src/tests/,
`*_tests.rs`, `tests.rs`, `test_support.rs` and `#[cfg(test)]` items) is excluded, and so are
the lines line coverage cannot measure (`source.unmeasured_lines`), which summary.md counts.
"""

import collections
import json
import os
import pickle
import sys
import tomllib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from source import Workspace  # noqa: E402

UNIT_KINDS = ("lib", "bin", "proc-macro")


def percent(part, whole):
    return f"{100 * part / whole:.1f}" if whole else "-"


def crate_of(rel):
    return rel.split("/")[1]


def module_path(rel):
    """`crates/k-rust/src/inner/parser.rs` -> `inner::parser`; lib.rs and main.rs -> ''."""
    if "/src/" not in rel:
        return None
    path = rel.split("/src/", 1)[1][:-3]
    if path.endswith("/mod"):
        path = path[:-4]
    return "" if path in ("lib", "main") else path.replace("/", "::")


def main():
    work, graph_path, suites = sys.argv[1], sys.argv[2], sys.argv[3:]
    workspace = Workspace(os.environ["COVERAGE_WORKSPACE"])
    out = os.path.join(work, "report")
    os.makedirs(out, exist_ok=True)

    all_lines = set()
    hits = collections.defaultdict(set)  # category -> {(rel, line)}
    per_test = {}  # suite -> {(binary id, test): set of (rel, line)}
    binaries = {}
    problems = []
    unmeasured = set()  # (rel, line) left out because line coverage cannot measure them
    for suite in suites:
        with open(os.path.join(work, "export", f"{suite}.pickle"), "rb") as handle:
            data = pickle.load(handle)
        problems += [f"{suite}: {p}" for p in data["problems"]]
        unmeasured |= data["unmeasured"]
        binaries[suite] = data["binaries"]
        for binary_id, files in data["lines"].items():
            kind = data["binaries"][binary_id]["kind"]
            category = "krust process" if kind == "krust" else "unit" if kind in UNIT_KINDS else "integration"
            for rel, counts in files.items():
                for line, count in counts.items():
                    all_lines.add((rel, line))
                    if count > 0:
                        hits[suite].add((rel, line))
                        hits[f"{suite} {category}"].add((rel, line))
        if data["tests"]:
            per_test[suite] = data["tests"]
    hits["all"] = set().union(*(hits[suite] for suite in suites))
    columns = [c for s in suites for c in (f"{s} unit", f"{s} integration", f"{s} krust process", s) if c in hits]
    columns.append("all")

    # Totals and per crate.
    totals = {"lines": len(all_lines), **{c: len(hits[c]) for c in columns}}
    totals["unmeasured lines left out"] = len(unmeasured)
    for suite, tests in per_test.items():
        union = {(rel, line) for found in tests.values() for rel, lines in found for line in lines}
        totals[f"{suite} per-test union"] = len(union)
        totals[f"{suite} per-test union outside the suite export"] = len(union - hits[suite])
        totals[f"{suite} suite export outside the per-test union"] = len(hits[suite] - union)
    with open(os.path.join(out, "totals.json"), "w") as handle:
        json.dump(totals, handle, indent=1)

    by_crate = collections.defaultdict(set)
    for key in all_lines:
        by_crate[crate_of(key[0])].add(key)
    with open(os.path.join(out, "summary.md"), "w") as handle:
        handle.write("# Line coverage of production code\n\n")
        handle.write(f"{len(hits['all'])} of {len(all_lines)} lines executed ({percent(len(hits['all']), len(all_lines))}%).\n\n")
        handle.write(
            f"{len(unmeasured)} further lines are left out of every count: the argument lines of "
            "multi-line calls of macros that expand each argument twice "
            "(`DUPLICATING_MACROS` in scripts/coverage/source.py), whose counts are those of a "
            "copy that need not have run. The line naming the macro carries the call's count.\n\n"
        )
        handle.write("| crate | lines | " + " | ".join(f"{c} %" for c in columns) + " | unexecuted |\n")
        handle.write("|---|---|" + "---|" * len(columns) + "---|\n")
        rows = [("**total**", all_lines)] + sorted(by_crate.items(), key=lambda item: -len(item[1]))
        for name, keys in rows:
            cells = " | ".join(percent(len(keys & hits[c]), len(keys)) for c in columns)
            handle.write(f"| {name} | {len(keys)} | {cells} | {len(keys - hits['all'])} |\n")
        handle.write("\n| count | lines |\n|---|---|\n")
        for name, value in totals.items():
            handle.write(f"| {name} | {value} |\n")
        handle.write(f"\n## Problems ({len(problems)})\n\n")
        for problem in problems:
            handle.write(f"- {problem}\n")

    # Files.
    by_file = collections.defaultdict(set)
    for key in all_lines:
        by_file[key[0]].add(key)
    with open(os.path.join(out, "files.md"), "w") as handle:
        handle.write("| file | lines | executed % | unexecuted |\n|---|---|---|---|\n")
        rows = [(rel, keys) for rel, keys in by_file.items() if len(keys) >= 150]
        for rel, keys in sorted(rows, key=lambda item: -len(item[1] - hits["all"])):
            executed = len(keys & hits["all"])
            handle.write(f"| {rel} | {len(keys)} | {percent(executed, len(keys))} | {len(keys) - executed} |\n")

    # Unexecuted ranges.
    with open(os.path.join(out, "uncovered.txt"), "w") as handle:
        for rel, keys in sorted(by_file.items()):
            lines = sorted(line for _, line in keys - hits["all"])
            ranges = []
            for line in lines:
                if ranges and line == ranges[-1][1] + 1:
                    ranges[-1][1] = line
                else:
                    ranges.append([line, line])
            for first, last in ranges:
                handle.write(f"{rel}:{first}-{last}\n" if first != last else f"{rel}:{first}\n")

    # Per test: lines executed and lines no other test of the suite executes.
    with open(os.path.join(out, "tests.tsv"), "w") as handle:
        handle.write("suite\tbinary\ttest\tlines\tunique\n")
        for suite, tests in per_test.items():
            count = collections.defaultdict(collections.Counter)
            for found in tests.values():
                for rel, lines in found:
                    count[rel].update(lines)
            for (binary_id, name), found in sorted(tests.items()):
                executed = sum(len(lines) for _, lines in found)
                unique = sum(1 for rel, lines in found for line in lines if count[rel][line] == 1)
                handle.write(f"{suite}\t{binary_id}\t{name}\t{executed}\t{unique}\n")

    # Algorithm cards.
    with open(graph_path, "rb") as handle:
        graph = tomllib.load(handle)
    algorithms = [node for node in graph.get("node", []) if node["kind"] == "algorithm"]
    site_owner = collections.defaultdict(list)  # (rel, line) -> card ids
    cards = []
    for node in algorithms:
        lines = set()
        unresolved = []
        for site in node.get("sites", []):
            spans = workspace.site_spans(site["file"], site["symbol"])
            if not spans:
                unresolved.append(f"{site['file']}:{site['symbol']}")
            for first, last in spans:
                lines.update((site["file"], line) for line in range(first, last + 1))
        lines &= all_lines
        for key in lines:
            site_owner[key].append(node["id"])
        cards.append({"id": node["id"], "lines": lines, "unresolved": unresolved, "sites": node.get("sites", [])})
    site_owner_by_file = collections.defaultdict(dict)
    for (rel, line), owners in site_owner.items():
        site_owner_by_file[rel][line] = owners
    tests_of = collections.defaultdict(lambda: collections.defaultdict(set))  # card -> suite -> tests
    for suite, tests in per_test.items():
        for key, found in tests.items():
            touched = set()
            for rel, lines in found:
                owners = site_owner_by_file.get(rel)
                if owners:
                    for line in lines:
                        touched.update(owners.get(line, ()))
            for card in touched:
                tests_of[card][suite].add(key)
    unit_binaries = {
        suite: {b for b, d in described.items() if d["kind"] in UNIT_KINDS} for suite, described in binaries.items()
    }
    records = []
    for card in cards:
        n = len(card["lines"])
        record = {"id": card["id"], "site_lines": n, "unresolved_sites": card["unresolved"]}
        for column in columns:
            record[column] = len(card["lines"] & hits[column])
        for suite in per_test:
            executing = tests_of[card["id"]][suite]
            local = set()
            for binary_id, name in executing:
                if binary_id not in unit_binaries[suite]:
                    continue
                for site in card["sites"]:
                    path = module_path(site["file"])
                    package = binaries[suite][binary_id]["package"]
                    if path and package == crate_of(site["file"]) and name.startswith(path + "::"):
                        local.add((binary_id, name))
            record[f"{suite} tests"] = len(executing)
            record[f"{suite} module-local tests"] = len(local)
            record[f"{suite} module-local examples"] = sorted(f"{b} {t}" for b, t in local)[:3]
        records.append(record)
    with open(os.path.join(out, "cards.json"), "w") as handle:
        json.dump(records, handle, indent=1)
    test_columns = [c for s in per_test for c in (f"{s} tests", f"{s} module-local tests")]
    with open(os.path.join(out, "cards.md"), "w") as handle:
        handle.write("| card | site lines | " + " | ".join(f"{c} %" for c in columns) + " | unexecuted | ")
        handle.write(" | ".join(test_columns) + " | unresolved sites |\n")
        handle.write("|---|---|" + "---|" * (len(columns) + 1 + len(test_columns)) + "---|\n")
        for record in sorted(records, key=lambda r: (r["all"] / r["site_lines"]) if r["site_lines"] else 2):
            n = record["site_lines"]
            cells = " | ".join(percent(record[c], n) for c in columns)
            tests = " | ".join(str(record[c]) for c in test_columns)
            handle.write(f"| {record['id']} | {n} | {cells} | {n - record['all']} | {tests} | {', '.join(record['unresolved_sites'])} |\n")

    print(open(os.path.join(out, "summary.md")).read().split("\n## Problems")[0])
    print(f"{len(problems)} problems; reports in {out}")


if __name__ == "__main__":
    main()
