"""Receipt comparison and summary tables.

The comparison rule follows k-rust's `algo-graph diff`: each side of a cell
(port, stage, scenario) is its set of repetitions; a side's value of a
quantity is the median over its repetitions (the mean of the two middle
values for an even count) with the min..max range. A measured quantity is
`unreplicated` when either side has fewer than two repetitions, `within noise`
when the two closed ranges overlap, and otherwise `faster`/`slower` (times) or
`lower`/`higher` (memory). Deterministic quantities (exit status and `krs`
counters) are compared exactly: `exact` when every repetition of both sides
agrees, `changed` when both sides are constant but differ, and `varies` when
repetitions within a side disagree. There are no statistical tests; ranges
are run-to-run spread under one sequence, not confidence intervals.
"""

from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from typing import Any, Callable, Iterable, Mapping, Sequence


@dataclass(frozen=True)
class Spread:
    median: float
    min: float
    max: float

    @classmethod
    def of(cls, values: Sequence[float]) -> "Spread":
        if not values:
            return cls(0.0, 0.0, 0.0)
        ordered = sorted(values)
        middle = len(ordered) // 2
        median = ordered[middle] if len(ordered) % 2 else (ordered[middle - 1] + ordered[middle]) / 2
        return cls(median, ordered[0], ordered[-1])

    @property
    def constant(self) -> bool:
        return self.min == self.max

    def overlaps(self, other: "Spread") -> bool:
        return self.min <= other.max and other.min <= self.max


def classify(before: Spread, after: Spread, before_runs: int, after_runs: int, words=("faster", "slower")) -> str:
    if before_runs < 2 or after_runs < 2:
        return "unreplicated"
    if before.overlaps(after):
        return "within noise"
    return words[0] if after.max < before.min else words[1]


def classify_exact(before: Spread, after: Spread) -> str:
    if not before.constant or not after.constant:
        return "varies"
    return "exact" if before.median == after.median else "changed"


Key = tuple[str, str, str]


def cell_key(receipt: Mapping[str, Any]) -> Key:
    return (str(receipt["port"]), str(receipt["stage"]), str(receipt["scenario"]))


def group(receipts: Iterable[Mapping[str, Any]]) -> dict[Key, list[Mapping[str, Any]]]:
    cells: dict[Key, list[Mapping[str, Any]]] = defaultdict(list)
    for receipt in receipts:
        cells[cell_key(receipt)].append(receipt)
    return dict(cells)


def _span_totals(receipt: Mapping[str, Any]) -> dict[str, float]:
    timings = receipt.get("krs_timings") or {}
    totals: dict[str, float] = defaultdict(float)
    for span in timings.get("spans") or []:
        totals[span["id"]] += float(span["seconds"])
    for name in ("total_wall_seconds", "unattributed_seconds"):
        if isinstance(timings.get(name), (int, float)):
            totals[name] = float(timings[name])
    return dict(totals)


def _semantics_seconds(receipt: Mapping[str, Any]) -> float | None:
    cargo = receipt.get("cargo_timings") or {}
    package = receipt.get("package")
    durations = [
        float(unit["duration"])
        for unit in cargo.get("units") or []
        if unit.get("name") == package and isinstance(unit.get("duration"), (int, float))
    ]
    return sum(durations) if durations else None


MetricGetter = Callable[[Mapping[str, Any]], float | None]


def metrics(receipts: Sequence[Mapping[str, Any]]) -> list[tuple[str, str, MetricGetter]]:
    """(name, kind, getter) for every quantity present in any receipt; kind is time, memory, or exact."""

    rows: list[tuple[str, str, MetricGetter]] = [
        ("exit_status", "exact", lambda r: r.get("exit_status")),
        ("wall_seconds", "time", lambda r: r.get("wall_seconds")),
        ("user_seconds", "time", lambda r: r.get("user_seconds")),
        ("sys_seconds", "time", lambda r: r.get("sys_seconds")),
        ("peak_memory_bytes", "memory", lambda r: r.get("peak_memory_bytes")),
    ]
    if any(_semantics_seconds(r) is not None for r in receipts):
        rows.append(("cargo.semantics_crate_seconds", "time", _semantics_seconds))
    span_ids: dict[str, None] = {}
    counter_ids: dict[str, None] = {}
    for receipt in receipts:
        span_ids.update(dict.fromkeys(_span_totals(receipt)))
        counter_ids.update(dict.fromkeys(_counters(receipt)))
    for span in span_ids:
        rows.append((f"krs.{span}", "time", lambda r, s=span: _span_totals(r).get(s)))
    for counter in sorted(counter_ids):
        rows.append(
            (f"counter.{counter}", "exact", lambda r, c=counter: _counters(r).get(c))
        )
    return rows


def _counters(receipt: Mapping[str, Any]) -> dict[str, float]:
    """Counters from the `krs --counters` document, then any the timings document carries."""

    merged = dict((receipt.get("krs_timings") or {}).get("counters") or {})
    merged.update((receipt.get("krs_counters") or {}).get("counters") or {})
    return merged


def _values(receipts: Sequence[Mapping[str, Any]], getter: MetricGetter) -> list[float]:
    return [float(v) for v in (getter(r) for r in receipts) if isinstance(v, (int, float))]


def _format(kind: str, spread: Spread, runs: int) -> str:
    def one(value: float) -> str:
        if kind == "memory":
            return f"{value / 2**30:.2f}GiB" if value >= 2**30 else f"{value / 2**20:.1f}MiB"
        if kind == "time":
            return f"{value:.3f}s"
        return str(int(value)) if float(value).is_integer() else f"{value:g}"

    if runs == 0:
        return "-"
    if spread.constant:
        return one(spread.median)
    return f"{one(spread.median)} ({one(spread.min)}..{one(spread.max)})"


def _direction(receipt: Mapping[str, Any]) -> str:
    return str((receipt.get("scenario_detail") or {}).get("direction", ""))


def _exact_by_direction(a: Sequence[Mapping[str, Any]], b: Sequence[Mapping[str, Any]], getter: MetricGetter) -> str:
    """Exact comparison within each edit direction.

    Edit scenarios alternately apply and revert their edit, so deterministic
    quantities legitimately differ between the two directions; repetitions are
    compared only with repetitions of the same direction.
    """

    verdicts = set()
    for direction in sorted({_direction(r) for r in [*a, *b]}):
        va = _values([r for r in a if _direction(r) == direction], getter)
        vb = _values([r for r in b if _direction(r) == direction], getter)
        if not va or not vb:
            verdicts.add("absent on one side")
            continue
        verdicts.add(classify_exact(Spread.of(va), Spread.of(vb)))
    for verdict in ("varies", "absent on one side", "changed"):
        if verdict in verdicts:
            return verdict
    return "exact"


def compare(before: Sequence[Mapping[str, Any]], after: Sequence[Mapping[str, Any]]) -> tuple[list[dict[str, Any]], list[str]]:
    """Compare two receipt sets cell by cell; returns (rows, warnings)."""

    warnings: list[str] = []
    for label, side in (("A", before), ("B", after)):
        if any(r.get("profiling") for r in side) and not all(r.get("profiling") for r in side):
            warnings.append(f"side {label} mixes profiled and unprofiled receipts")
    if {bool(r.get("profiling")) for r in before} != {bool(r.get("profiling")) for r in after} and before and after:
        warnings.append("profiled receipts are never comparable with unprofiled ones; profiled cells are skipped")
    left, right = group(before), group(after)
    rows: list[dict[str, Any]] = []
    for key in sorted(set(left) | set(right)):
        a, b = left.get(key, []), right.get(key, [])
        if not a or not b:
            rows.append({"key": key, "metric": "*", "verdict": "only in " + ("B" if not a else "A"), "a": "", "b": ""})
            continue
        if any(bool(r.get("profiling")) for r in a) != any(bool(r.get("profiling")) for r in b):
            continue
        env_a = {tuple(sorted((r.get("environment") or {}).get("overrides", {}).items())) for r in a}
        env_b = {tuple(sorted((r.get("environment") or {}).get("overrides", {}).items())) for r in b}
        if env_a != env_b:
            warnings.append(f"{'/'.join(key)}: environment overrides differ: A={sorted(env_a)} B={sorted(env_b)}")
        for name, kind, getter in metrics([*a, *b]):
            va, vb = _values(a, getter), _values(b, getter)
            if not va and not vb:
                continue
            if not va or not vb:
                rows.append({"key": key, "metric": name, "verdict": "absent on one side",
                             "a": _format(kind, Spread.of(va), len(va)), "b": _format(kind, Spread.of(vb), len(vb))})
                continue
            sa, sb = Spread.of(va), Spread.of(vb)
            if kind == "exact":
                verdict = _exact_by_direction(a, b, getter)
            else:
                words = ("lower", "higher") if kind == "memory" else ("faster", "slower")
                verdict = classify(sa, sb, len(va), len(vb), words)
            rows.append({"key": key, "metric": name, "verdict": verdict, "delta": sb.median - sa.median,
                         "a": f"{_format(kind, sa, len(va))} n={len(va)}",
                         "b": f"{_format(kind, sb, len(vb))} n={len(vb)}"})
    return rows, warnings


def render_compare(rows: Sequence[Mapping[str, Any]], warnings: Sequence[str]) -> str:
    lines = [f"warning: {warning}" for warning in warnings]
    by_port: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in rows:
        by_port[row["key"][0]].append(row)
    for port in sorted(by_port):
        lines.append(f"\n== {port} ==")
        table = [("stage", "scenario", "metric", "A", "B", "verdict")]
        for row in by_port[port]:
            table.append((row["key"][1], row["key"][2], row["metric"], row["a"], row["b"], row["verdict"]))
        lines.extend(_table(table))
    counts: dict[str, int] = defaultdict(int)
    for row in rows:
        counts[row["verdict"]] += 1
    lines.append("\nverdicts: " + ", ".join(f"{verdict}={count}" for verdict, count in sorted(counts.items())))
    return "\n".join(lines).lstrip("\n")


STAGE_ORDER = ("krs-check", "krs-emit-k", "krs-build", "cargo-check", "collector-build")
SCENARIO_ORDER = ("cold", "warm", "no-op", "touch", "edit-rule", "edit-enum")


def _order(key: Key) -> tuple[Any, ...]:
    port, stage, scenario = key
    return (
        port,
        STAGE_ORDER.index(stage) if stage in STAGE_ORDER else len(STAGE_ORDER), stage,
        SCENARIO_ORDER.index(scenario) if scenario in SCENARIO_ORDER else len(SCENARIO_ORDER), scenario,
    )


def render_summary(receipts: Sequence[Mapping[str, Any]]) -> str:
    """One table per port: every cell's wall, CPU, peak memory, and exit statuses."""

    cells = group(receipts)
    lines: list[str] = []
    for port in sorted({key[0] for key in cells}):
        lines.append(f"== {port} ==")
        table = [("stage", "scenario", "n", "wall", "user", "sys", "peak", "semantics crate", "exit")]
        for key in sorted((k for k in cells if k[0] == port), key=_order):
            runs = cells[key]
            row = [key[1], key[2], str(len(runs))]
            for getter, kind in (
                (lambda r: r.get("wall_seconds"), "time"),
                (lambda r: r.get("user_seconds"), "time"),
                (lambda r: r.get("sys_seconds"), "time"),
                (lambda r: r.get("peak_memory_bytes"), "memory"),
                (_semantics_seconds, "time"),
            ):
                values = _values(runs, getter)
                row.append(_format(kind, Spread.of(values), len(values)))
            row.append(",".join(str(r.get("exit_status")) for r in runs))
            table.append(tuple(row))
        lines.extend(_table(table))
        lines.append("")
    return "\n".join(lines).rstrip()


def _table(rows: Sequence[Sequence[str]]) -> list[str]:
    widths = [max(len(str(row[i])) for row in rows) for i in range(len(rows[0]))]
    out = []
    for index, row in enumerate(rows):
        out.append("  ".join(str(cell).ljust(width) for cell, width in zip(row, widths)).rstrip())
        if index == 0:
            out.append("  ".join("-" * width for width in widths))
    return out
