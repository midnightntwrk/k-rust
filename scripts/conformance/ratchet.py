#!/usr/bin/env python3
"""Build and append versioned regression-new conformance ratchet entries."""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib


RANK = {
    "reference-error": -1,
    "krust-error": 0,
    "mismatch": 1,
    "krust-unsupported": 2,
    "skipped-with-reason": 2,
    "match": 3,
}


class RatchetError(Exception):
    pass


def load_toml(path: Path, description: str) -> dict:
    try:
        with path.open("rb") as source:
            return tomllib.load(source)
    except (OSError, tomllib.TOMLDecodeError) as error:
        raise RatchetError(f"cannot read {description} {path}: {error}") from error


def expectation_map(document: dict) -> dict[str, dict]:
    rows = document.get("case")
    if not isinstance(rows, list):
        raise RatchetError("expectations contain no [[case]] rows")
    mapped = {}
    for row in rows:
        name = row.get("name")
        if not isinstance(name, str) or not name:
            raise RatchetError("expectation case has no name")
        if name in mapped:
            raise RatchetError(f"duplicate expectation case: {name}")
        if "accepted_verdict" in row and row["accepted_verdict"] not in RANK:
            raise RatchetError(f"case {name} has unknown accepted verdict: {row['accepted_verdict']!r}")
        if "accepted_verdict" in row and not isinstance(row.get("accepted_stage"), str):
            raise RatchetError(f"case {name} has no accepted stage")
        mapped[name] = row
    return mapped


def result_cases(document: dict, expectations: dict[str, dict]) -> list[dict]:
    rows = document.get("case")
    if not isinstance(rows, list) or not rows:
        raise RatchetError("results contain no [[case]] rows")
    seen = set()
    for row in rows:
        name = row.get("name")
        if not isinstance(name, str) or not name:
            raise RatchetError("result case has no name")
        if name in seen:
            raise RatchetError(f"duplicate result case: {name}")
        if name not in expectations:
            raise RatchetError(f"result case has no expectation: {name}")
        verdict = row.get("verdict")
        if verdict not in RANK:
            raise RatchetError(f"case {name} has unknown verdict: {verdict!r}")
        seen.add(name)
    return rows


def string_array(values: list[str]) -> str:
    return "[" + ", ".join(json.dumps(value, ensure_ascii=False) for value in values) + "]"


def inline_counts(counts: Counter) -> str:
    ordered = [
        "match",
        "mismatch",
        "krust-error",
        "krust-unsupported",
        "skipped-with-reason",
        "reference-error",
    ]
    fields = [f"{json.dumps(key)} = {counts.get(key, 0)}" for key in ordered]
    return "{ " + ", ".join(fields) + " }"


def render_entry(run: dict) -> str:
    lines = ["[[run]]"]
    scalar_order = [
        "sequence",
        "timestamp_utc",
        "label",
        "workspace_revision",
        "k_revision",
        "driver_version",
        "krust_sha256",
        "test_binary_sha256",
        "selection",
        "jobs",
        "wall_seconds",
        "peak_rss_mib",
    ]
    for key in scalar_order:
        value = run[key]
        if isinstance(value, str):
            lines.append(f"{key} = {json.dumps(value, ensure_ascii=False)}")
        else:
            lines.append(f"{key} = {value}")
    lines.append(f"counts = {inline_counts(run['counts'])}")
    for key in [
        "regressions",
        "below_floor",
        "improvements",
        "driver_deltas",
        "oracle_changes",
        "overdue",
        "excluded",
        "promotion_candidates",
    ]:
        lines.append(f"{key} = {string_array(run[key])}")
    lines.append(f"artifacts = {json.dumps(run['artifacts'], ensure_ascii=False)}")
    lines.append("")
    for case in run["case"]:
        lines += [
            "[[run.case]]",
            f"name = {json.dumps(case['name'], ensure_ascii=False)}",
            f"verdict = {json.dumps(case['verdict'])}",
            f"stage = {json.dumps(case['stage'])}",
            f"fallback_verdict = {json.dumps(case['fallback_verdict'])}",
            f"rank = {case['rank']}",
            f"previous_rank = {case['previous_rank']}",
            f"floor_rank = {case['floor_rank']}",
            f"delta = {json.dumps(case['delta'])}",
            f"tickets = {string_array(case['tickets'])}",
            f"exclusion = {json.dumps(case['exclusion'], ensure_ascii=False)}",
            "",
        ]
    return "\n".join(lines)


def write_new_log(path: Path, entry: str) -> None:
    if path.exists():
        raise RatchetError(f"ratchet log already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    atomic_write(path, "version = 1\n\n" + entry.rstrip() + "\n")


def append_log(path: Path, entry: str) -> None:
    if not path.is_file():
        raise RatchetError(f"seed entry 0 before appending: {path}")
    current = path.read_text()
    document = load_toml(path, "ratchet log")
    if document.get("version") != 1:
        raise RatchetError(f"ratchet log does not declare version 1: {path}")
    atomic_write(path, current.rstrip() + "\n\n" + entry.rstrip() + "\n")


def atomic_write(path: Path, body: str) -> None:
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w") as output:
            output.write(body)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def matching_step_exclusion(result: dict, expectation: dict) -> str:
    if expectation.get("exclusion"):
        return expectation["exclusion"]
    failing = next(
        (
            step
            for step in result.get("step", [])
            if step.get("verdict") == result.get("verdict")
        ),
        None,
    )
    if failing is None:
        return ""
    for exclusion in expectation.get("step_exclusions", []):
        selectors = [key for key in ("test", "out", "step") if key in exclusion]
        if selectors and all(failing.get(key) == exclusion[key] for key in selectors):
            return exclusion.get("exclusion", "")
    return ""


def ticket_states(path: Path | None) -> dict[str, str]:
    if path is None or not path.is_file():
        return {}
    document = load_toml(path, "implementation status")
    return {
        row["id"]: row.get("state", "")
        for row in document.get("ticket", [])
        if isinstance(row.get("id"), str)
    }


def tickets_landed(tickets: list[str], states: dict[str, str]) -> bool:
    return bool(tickets) and all(
        states.get(ticket.split(":", 1)[0]) in {"implemented", "verified"}
        for ticket in tickets
    )


def previous_measurement(runs: list[dict], name: str) -> tuple[dict | None, dict | None]:
    for run in reversed(runs):
        for case in run.get("case", []):
            if case.get("name") == name:
                return run, case
    return None, None


def first_measurement(runs: list[dict], name: str) -> tuple[dict | None, dict | None]:
    """The stage-1 floor of a case: entry 0 when it measured the case, else its first entry."""
    for run in runs:
        for case in run.get("case", []):
            if case.get("name") == name:
                return run, case
    return None, None


def is_below_floor(rank: int, floor_rank: int) -> bool:
    return rank >= 0 and floor_rank >= 0 and rank < floor_rank


def classify_delta(
    previous_run: dict | None,
    previous_case: dict | None,
    floor_case: dict | None,
    verdict: str,
    driver_version: str,
) -> tuple[int, int, str, bool]:
    """Classify a measurement against the previous one and the required floor.

    Returns (previous_rank, floor_rank, delta, driver_changed). A decrease below the floor
    is a regression whatever the driver version; a decrease that stays at or above the
    floor is a driver-delta when the previous measurement used another driver version.
    """
    if previous_case is None or previous_run is None:
        return -1, -1, "new", False
    previous_rank = previous_case["rank"]
    floor_rank = floor_case["rank"] if floor_case is not None else previous_rank
    rank = RANK[verdict]
    driver_changed = previous_run.get("driver_version") != driver_version
    if previous_rank == rank:
        return previous_rank, floor_rank, "same", False
    if previous_rank == -1 or rank == -1:
        return previous_rank, floor_rank, "oracle-changed", False
    if rank > previous_rank:
        return previous_rank, floor_rank, "improvement", driver_changed
    if is_below_floor(rank, floor_rank):
        return previous_rank, floor_rank, "regression", driver_changed
    if driver_changed:
        return previous_rank, floor_rank, "driver-delta", True
    return previous_rank, floor_rank, "regression", False


def build_run(
    *,
    sequence: int,
    label: str,
    workspace_revision: str,
    k_revision: str,
    driver_version: str,
    krust_sha256: str,
    test_binary_sha256: str,
    selection: str,
    jobs: int,
    wall_seconds: float,
    peak_rss_mib: int,
    artifacts: str,
    results: list[dict],
    expectations: dict[str, dict],
    previous_runs: list[dict],
    states: dict[str, str],
    timestamp_utc: str | None = None,
) -> dict:
    rows = []
    regressions = []
    below_floor = []
    improvements = []
    driver_deltas = []
    oracle_changes = []
    overdue = []
    excluded = []
    promotion_candidates = []
    for result in sorted(results, key=lambda row: row["name"]):
        name = result["name"]
        expectation = expectations[name]
        verdict = result["verdict"]
        rank = RANK[verdict]
        previous_run, previous_case = previous_measurement(previous_runs, name)
        _, floor_case = first_measurement(previous_runs, name)
        accepted_rank = RANK.get(expectation.get("accepted_verdict"), -1)
        if accepted_rank > (floor_case["rank"] if floor_case else -1):
            floor_case = {"rank": accepted_rank}
        previous_rank, floor_rank, delta, driver_changed = classify_delta(
            previous_run, previous_case, floor_case, verdict, driver_version
        )
        floor_rank = max(floor_rank, accepted_rank)
        exclusion = matching_step_exclusion(result, expectation)
        tickets = list(expectation.get("tickets", []))
        if delta == "regression" and not exclusion:
            regressions.append(name)
        if is_below_floor(rank, floor_rank) and not exclusion:
            below_floor.append(name)
        if delta == "improvement":
            improvements.append(name)
        if driver_changed:
            driver_deltas.append(name)
        if delta == "oracle-changed":
            oracle_changes.append(name)
        if exclusion:
            excluded.append(name)
        if (
            rank < RANK["match"]
            and rank >= 0
            and not exclusion
            and expectation.get("unexplained") is not True
            and tickets_landed(tickets, states)
        ):
            overdue.append(name)
        if (
            rank == RANK["match"]
            and previous_case is not None
            and previous_case.get("rank") == RANK["match"]
            and not expectation.get("exclusion")
            and not expectation.get("promoted_to")
            and tickets_landed(tickets, states)
        ):
            promotion_candidates.append(name)
        rows.append(
            {
                "name": name,
                "verdict": verdict,
                "stage": result.get("stage", "none"),
                "fallback_verdict": result.get("fallback_verdict", ""),
                "rank": rank,
                "previous_rank": previous_rank,
                "floor_rank": floor_rank,
                "delta": delta,
                "tickets": tickets,
                "exclusion": exclusion,
            }
        )
    return {
        "sequence": sequence,
        "timestamp_utc": timestamp_utc
        or datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
        "label": label,
        "workspace_revision": workspace_revision,
        "k_revision": k_revision,
        "driver_version": driver_version,
        "krust_sha256": krust_sha256,
        "test_binary_sha256": test_binary_sha256,
        "selection": selection,
        "jobs": jobs,
        "wall_seconds": round(wall_seconds, 1),
        "peak_rss_mib": peak_rss_mib,
        "counts": Counter(result["verdict"] for result in results),
        "regressions": regressions,
        "below_floor": below_floor,
        "improvements": improvements,
        "driver_deltas": driver_deltas,
        "oracle_changes": oracle_changes,
        "overdue": overdue,
        "excluded": excluded,
        "promotion_candidates": promotion_candidates,
        "artifacts": artifacts,
        "case": rows,
    }


def print_pr_block(run: dict) -> None:
    print("### Conformance ratchet")
    print()
    print("| case | floor | previous | now | delta | tickets |")
    print("|---|---:|---:|---:|---|---|")
    for case in run["case"]:
        tickets = ", ".join(case["tickets"])
        exclusion = f" (excluded: {case['exclusion']})" if case["exclusion"] else ""
        print(
            f"| {case['name']} | {case['floor_rank']} | {case['previous_rank']} | "
            f"{case['rank']} | {case['delta']}{exclusion} | {tickets} |"
        )
    print()
    print(f"regressions: {len(run['regressions'])}")
    print(f"below required floor: {string_array(run['below_floor'])}")
    print(f"improvements: {len(run['improvements'])}")
    print(f"driver deltas: {len(run['driver_deltas'])}")
    print(f"oracle changes: {len(run['oracle_changes'])}")
    print(f"overdue: {run['overdue']}")
    print(f"excluded (measured): {len(run['excluded'])}")
    print(f"wall: {run['wall_seconds']} s")
    print(f"peak RSS: {run['peak_rss_mib']} MiB")
    print(f"driver_version: {run['driver_version']}")


def command_seed(args: argparse.Namespace) -> int:
    expectation_document = load_toml(args.expectations, "expectations")
    expectations = expectation_map(expectation_document)
    if args.results is None:
        missing = [name for name, row in expectations.items() if "accepted_verdict" not in row]
        if missing:
            raise RatchetError(f"cases without an acceptance baseline: {', '.join(missing)}")
        results = [
            {"name": name, "verdict": row["accepted_verdict"], "stage": row["accepted_stage"]}
            for name, row in expectations.items()
        ]
        baseline = expectation_document.get("acceptance", {})
    else:
        results = result_cases(load_toml(args.results, "results"), expectations)
        baseline = expectation_document.get("baseline", {})
    run = build_run(
        sequence=0,
        label=args.label,
        workspace_revision=baseline.get("workspace_revision", ""),
        k_revision=baseline.get("k_revision", ""),
        driver_version="accepted-baseline" if args.results is None else "00-baseline",
        krust_sha256="",
        test_binary_sha256="",
        selection="all",
        jobs=2,
        wall_seconds=0.0 if args.results is None else 4060.0,
        peak_rss_mib=-1,
        artifacts=baseline.get("artifacts", str(args.expectations)),
        results=results,
        expectations=expectations,
        previous_runs=[],
        states={},
        timestamp_utc=baseline.get("timestamp_utc"),
    )
    write_new_log(args.log, render_entry(run))
    print_pr_block(run)
    return 3 if run["below_floor"] else 0


def command_append(args: argparse.Namespace) -> int:
    expectation_document = load_toml(args.expectations, "expectations")
    expectations = expectation_map(expectation_document)
    results = result_cases(load_toml(args.results, "results"), expectations)
    log_document = load_toml(args.log, "ratchet log")
    if log_document.get("version") != 1:
        raise RatchetError(f"ratchet log does not declare version 1: {args.log}")
    previous_runs = log_document.get("run", [])
    states = ticket_states(args.status)
    run = build_run(
        sequence=len(previous_runs),
        label=args.label,
        workspace_revision=args.workspace_revision,
        k_revision=args.k_revision,
        driver_version=args.driver_version,
        krust_sha256=args.krust_sha256,
        test_binary_sha256=args.test_binary_sha256,
        selection=args.selection,
        jobs=args.jobs,
        wall_seconds=args.wall_seconds,
        peak_rss_mib=args.peak_rss_mib,
        artifacts=args.artifacts,
        results=results,
        expectations=expectations,
        previous_runs=previous_runs,
        states=states,
    )
    append_log(args.log, render_entry(run))
    print_pr_block(run)
    return 3 if run["regressions"] or run["below_floor"] else 0


def command_select(args: argparse.Namespace) -> int:
    expectations = expectation_map(load_toml(args.expectations, "expectations"))
    selected = set()
    selected.update(args.cases)
    for ticket in args.ticket:
        selected.update(
            name
            for name, row in expectations.items()
            if ticket in row.get("tickets", [])
        )
    for stage in args.stage:
        selected.update(
            name
            for name, row in expectations.items()
            if row.get("baseline_stage") == stage
        )
    if args.all:
        selected.update(expectations)
    unknown = sorted(selected - expectations.keys())
    if unknown:
        raise RatchetError(f"unknown conformance case(s): {', '.join(unknown)}")
    for name in expectations:
        if name in selected:
            print(name)
    return 0


def command_audit(args: argparse.Namespace) -> int:
    """List cases below the greater of their first rank and versioned acceptance rank."""
    document = load_toml(args.log, "ratchet log")
    expectations = expectation_map(load_toml(args.expectations, "expectations")) if args.expectations else {}
    if document.get("version") != 1:
        raise RatchetError(f"ratchet log does not declare version 1: {args.log}")
    runs = document.get("run", [])
    if args.sequence is not None:
        selected = [run for run in runs if run.get("sequence") == args.sequence]
        if not selected:
            raise RatchetError(f"ratchet log has no run with sequence {args.sequence}")
        latest = {case["name"]: (selected[0], case) for case in selected[0].get("case", [])}
    else:
        latest = {}
        for run in runs:
            for case in run.get("case", []):
                latest[case["name"]] = (run, case)
    rows = []
    for name in sorted(latest):
        run, case = latest[name]
        _, floor_case = first_measurement(runs, name)
        floor_rank = floor_case["rank"] if floor_case is not None else -1
        floor_rank = max(floor_rank, RANK.get(expectations.get(name, {}).get("accepted_verdict"), -1))
        if is_below_floor(case["rank"], floor_rank):
            rows.append((name, floor_rank, run, case))
    scope = f"run {args.sequence}" if args.sequence is not None else "latest measurement per case"
    print(f"### Conformance required floor audit ({scope}, {len(latest)} cases)")
    print()
    print("| case | floor | rank | run | verdict | tickets | exclusion |")
    print("|---|---:|---:|---:|---|---|---|")
    failing = 0
    for name, floor_rank, run, case in rows:
        tickets = ", ".join(case.get("tickets", []))
        exclusion = case.get("exclusion", "")
        if not exclusion:
            failing += 1
        print(
            f"| {name} | {floor_rank} | {case['rank']} | {run.get('sequence')} | "
            f"{case['verdict']} | {tickets} | {exclusion} |"
        )
    print()
    print(f"below floor: {len(rows)} ({failing} non-excluded)")
    return 3 if failing else 0


def command_next_sequence(args: argparse.Namespace) -> int:
    document = load_toml(args.log, "ratchet log")
    if document.get("version") != 1:
        raise RatchetError(f"ratchet log does not declare version 1: {args.log}")
    print(len(document.get("run", [])))
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser()
    subparsers = root.add_subparsers(dest="command", required=True)

    seed = subparsers.add_parser("seed")
    seed.add_argument("--results", type=Path, help="omit to seed from versioned acceptance expectations")
    seed.add_argument("--expectations", type=Path, required=True)
    seed.add_argument("--log", type=Path, required=True)
    seed.add_argument("--label", required=True)
    seed.set_defaults(run=command_seed)

    append = subparsers.add_parser("append")
    append.add_argument("--results", type=Path, required=True)
    append.add_argument("--expectations", type=Path, required=True)
    append.add_argument("--status", type=Path)
    append.add_argument("--log", type=Path, required=True)
    append.add_argument("--label", required=True)
    append.add_argument("--workspace-revision", required=True)
    append.add_argument("--k-revision", required=True)
    append.add_argument("--driver-version", required=True)
    append.add_argument("--krust-sha256", required=True)
    append.add_argument("--test-binary-sha256", required=True)
    append.add_argument("--selection", required=True)
    append.add_argument("--jobs", type=int, required=True)
    append.add_argument("--wall-seconds", type=float, required=True)
    append.add_argument("--peak-rss-mib", type=int, required=True)
    append.add_argument("--artifacts", required=True)
    append.set_defaults(run=command_append)

    select = subparsers.add_parser("select")
    select.add_argument("--expectations", type=Path, required=True)
    select.add_argument("--cases", nargs="*", default=[])
    select.add_argument("--ticket", action="append", default=[])
    select.add_argument("--stage", action="append", default=[])
    select.add_argument("--all", action="store_true")
    select.set_defaults(run=command_select)

    audit = subparsers.add_parser("audit")
    audit.add_argument("--log", type=Path, required=True)
    audit.add_argument("--sequence", type=int)
    audit.add_argument("--expectations", type=Path, default=Path(__file__).with_name("expectations.toml"))
    audit.set_defaults(run=command_audit)

    sequence = subparsers.add_parser("next-sequence")
    sequence.add_argument("--log", type=Path, required=True)
    sequence.set_defaults(run=command_next_sequence)
    return root


def main() -> int:
    args = parser().parse_args()
    try:
        return args.run(args)
    except RatchetError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
