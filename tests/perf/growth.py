"""Growth fits over ladder receipts, as in k-rust's algo-graph atlas.

A ladder measures one metric at several values of a size parameter. For each
metric the fit is the ordinary least-squares line through
`(ln size, ln value)` over the rungs where both are positive, with R² and the
`top slope` between the two largest sizes (k-rust `fit_power_law` and
`RunFit`). A rung's value is the median of its repetitions.

A slope is `flagged` when the fit slope or the top slope exceeds the
threshold (1.2 by default). Time metrics whose largest median is below the
noise floor are fitted but never flagged: sub-100-ms spans on a loaded host
have no meaningful exponent. Counters are deterministic and always eligible.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import math
import re
from typing import Any, Iterable, Mapping, Sequence

from perf.compare import Spread

THRESHOLD = 1.2
TIME_FLOOR_SECONDS = 0.1

X_AXES = (
    "counter.descriptors.total",
    "counter.provenance.anchors",
    "counter.provenance.origin_frames",
    "counter.bundle.bytes",
    "counter.definition.sentences",
    "source.bytes",
)
"""Secondary x-axes: deterministic work sizes that a metric may be fitted against instead of the parameter."""

CORE_METRICS = (
    "wall_seconds",
    "cpu_seconds",
    "peak_memory_bytes",
    "span.collector.cargo",
    "span.collector.run",
    "span.collector.resolve.provenance",
    "span.native.compile",
    "llvm_lines.total",
    "counter.bundle.bytes",
)
"""The metrics fitted against every secondary x-axis."""


@dataclass(frozen=True)
class Fit:
    slope: float
    intercept: float
    points: int
    r_squared: float | None
    fewer_than_three: bool


def fit_power_law(points: Iterable[tuple[float, float]]) -> Fit | None:
    """Least squares of `ln(value)` on `ln(size)` over the points where both are positive.

    None with fewer than two such points or when they share one size.
    """

    logs = [(math.log(x), math.log(y)) for x, y in points if x > 0 and y > 0]
    if len(logs) < 2:
        return None
    count = len(logs)
    mean_x = sum(x for x, _ in logs) / count
    mean_y = sum(y for _, y in logs) / count
    sxx = sum((x - mean_x) ** 2 for x, _ in logs)
    if sxx == 0:
        return None
    sxy = sum((x - mean_x) * (y - mean_y) for x, y in logs)
    slope = sxy / sxx
    intercept = mean_y - slope * mean_x
    total = sum((y - mean_y) ** 2 for _, y in logs)
    residual = sum((y - intercept - slope * x) ** 2 for x, y in logs)
    return Fit(slope, intercept, count, (1 - residual / total) if total > 0 else None, count < 3)


@dataclass(frozen=True)
class Growth:
    metric: str
    x: str
    points: list[tuple[float, float]]
    fit: Fit | None
    top_slope: float | None
    top_sizes: list[float]
    below_floor: bool

    def exceeds(self, threshold: float = THRESHOLD) -> bool:
        if self.below_floor:
            return False
        return bool((self.fit and self.fit.slope > threshold) or (self.top_slope is not None and self.top_slope > threshold))

    def to_json(self) -> dict[str, Any]:
        document = asdict(self)
        document["points"] = [list(point) for point in self.points]
        return document


def growth(metric: str, x: str, points: Sequence[tuple[float, float]]) -> Growth:
    """Fit one metric; points are `(size, median)` pairs, any order."""

    by_size: dict[float, float] = {}
    for size, value in points:
        by_size[size] = value
    ordered = sorted(by_size.items())
    positive = [(size, value) for size, value in ordered if size > 0 and value > 0]
    top = fit_power_law(positive[-2:]) if len(positive) >= 2 else None
    floor = is_time(metric) and (max((value for _, value in ordered), default=0.0) < TIME_FLOOR_SECONDS)
    return Growth(metric, x, ordered, fit_power_law(positive), None if top is None else top.slope,
                  [size for size, _ in positive[-2:]] if top is not None else [], floor)


def is_time(metric: str) -> bool:
    return metric.endswith("_seconds") or metric.startswith("span.")


# --- metrics of one receipt -------------------------------------------------------


def receipt_metrics(receipt: Mapping[str, Any]) -> dict[str, float]:
    """Every fittable quantity of one ladder receipt, by metric name."""

    values: dict[str, float] = {}
    for name in ("wall_seconds", "peak_memory_bytes"):
        if isinstance(receipt.get(name), (int, float)):
            values[name] = float(receipt[name])
    user, system = receipt.get("user_seconds"), receipt.get("sys_seconds")
    if isinstance(user, (int, float)) and isinstance(system, (int, float)):
        values["cpu_seconds"] = float(user) + float(system)
    timings = receipt.get("krs_timings") or {}
    for span in timings.get("spans") or []:
        key = f"span.{span['id']}"
        values[key] = values.get(key, 0.0) + float(span["seconds"])
    counters = dict((receipt.get("krs_counters") or {}).get("counters") or {})
    for name, value in counters.items():
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            values[f"counter.{name}"] = float(value)
    ladder = receipt.get("ladder") or {}
    for name in ("bytes", "lines"):
        if isinstance(ladder.get(f"source_{name}"), (int, float)):
            values[f"source.{name}"] = float(ladder[f"source_{name}"])
    llvm = ladder.get("llvm_lines") or {}
    for name in ("total", "copies"):
        if isinstance(llvm.get(name), (int, float)):
            values[f"llvm_lines.{name}"] = float(llvm[name])
    return values


def rung_medians(receipts: Sequence[Mapping[str, Any]]) -> dict[float, dict[str, float]]:
    """Per ladder value, the median of each metric over that value's successful repetitions."""

    by_value: dict[float, list[dict[str, float]]] = {}
    for receipt in receipts:
        if receipt.get("exit_status") != 0:
            continue
        value = float(receipt["ladder"]["value"])
        by_value.setdefault(value, []).append(receipt_metrics(receipt))
    medians: dict[float, dict[str, float]] = {}
    for value, runs in sorted(by_value.items()):
        names = sorted({name for run in runs for name in run})
        medians[value] = {name: Spread.of([run[name] for run in runs if name in run]).median for name in names}
    return medians


# --- llvm-lines function groups ------------------------------------------------------


_HASH = re.compile(r"::h[0-9a-f]{16}$|[0-9a-f]{16,}")
_DIGITS = re.compile(r"[0-9]+")


def function_group(name: str) -> str:
    """A generated-function group: the llvm-lines name with hashes and numbers normalized."""

    return _DIGITS.sub("N", _HASH.sub("H", name))


def group_lines(functions: Iterable[Mapping[str, Any]]) -> dict[str, float]:
    groups: dict[str, float] = {}
    for function in functions:
        key = function_group(str(function.get("name", "")))
        groups[key] = groups.get(key, 0.0) + float(function.get("lines", 0))
    return groups


def largest_growth_group(small: Iterable[Mapping[str, Any]], large: Iterable[Mapping[str, Any]]) -> tuple[str, float] | None:
    """The llvm-lines function group whose lines grew most between two rungs."""

    before, after = group_lines(small), group_lines(large)
    deltas = {name: after.get(name, 0.0) - before.get(name, 0.0) for name in after}
    if not deltas:
        return None
    name = max(deltas, key=lambda key: deltas[key])
    return name, deltas[name]


# --- a whole ladder -------------------------------------------------------------------


def analyse(receipts: Sequence[Mapping[str, Any]], threshold: float = THRESHOLD) -> dict[str, Any]:
    """Fits of every metric against the ladder parameter, and of the core metrics against each x-axis."""

    medians = rung_medians(receipts)
    metrics = sorted({name for values in medians.values() for name in values})
    by_param = [growth(name, "param", [(value, values[name]) for value, values in medians.items() if name in values])
                for name in metrics]
    by_axis = []
    for axis in X_AXES:
        for name in CORE_METRICS:
            points = [(values[axis], values[name]) for values in medians.values() if axis in values and name in values]
            if len({x for x, _ in points}) >= 2:
                by_axis.append(growth(name, axis, points))
    flagged = [item for item in by_param + by_axis if item.exceeds(threshold)]
    dominant = dominant_leaf_span(receipts, medians)
    return {
        "threshold": threshold,
        "time_floor_seconds": TIME_FLOOR_SECONDS,
        "values": list(medians),
        "medians": {str(value): values for value, values in medians.items()},
        "by_param": [item.to_json() for item in by_param],
        "by_axis": [item.to_json() for item in by_axis],
        "dominant_leaf_span": dominant,
        "flagged": [{"metric": item.metric, "x": item.x, "stage": stage_of(item.metric, dominant),
                     "slope": None if item.fit is None else item.fit.slope, "top_slope": item.top_slope}
                    for item in flagged],
    }


def leaf_spans(receipts: Sequence[Mapping[str, Any]]) -> set[str]:
    """Span ids that have no child span in some receipt's pre-order span list."""

    leaves: set[str] = set()
    parents: set[str] = set()
    for receipt in receipts:
        spans = (receipt.get("krs_timings") or {}).get("spans") or []
        for index, span in enumerate(spans):
            following = spans[index + 1]["depth"] if index + 1 < len(spans) else -1
            (parents if following > span["depth"] else leaves).add(span["id"])
    return leaves - parents


def dominant_leaf_span(receipts: Sequence[Mapping[str, Any]],
                       medians: Mapping[float, Mapping[str, float]]) -> dict[str, Any] | None:
    """The leaf span whose median grew most between the two largest measured values."""

    if len(medians) < 2:
        return None
    small, large = sorted(medians)[-2:]
    deltas = {
        span: medians[large].get(f"span.{span}", 0.0) - medians[small].get(f"span.{span}", 0.0)
        for span in leaf_spans(receipts)
    }
    if not deltas:
        return None
    span = max(deltas, key=lambda key: deltas[key])
    return {"span": span, "seconds_added": round(deltas[span], 3), "from": small, "to": large}


def stage_of(metric: str, dominant: Mapping[str, Any] | None = None) -> str:
    """The pipeline stage a metric belongs to, for naming a flagged slope.

    A whole-run metric names the leaf span that grew most between the two
    largest values, which is where the added time went.
    """

    if metric.startswith("span."):
        return metric[len("span."):]
    if metric.startswith("counter."):
        return "counter:" + metric[len("counter."):].split(".")[0]
    if metric.startswith("llvm_lines."):
        return "rustc codegen of the definition crate (cargo llvm-lines)"
    if metric.startswith("source."):
        return "generated source"
    if dominant is not None and metric in ("wall_seconds", "cpu_seconds", "peak_memory_bytes"):
        return (f"whole krs run (process tree); largest-growth leaf span `{dominant['span']}` "
                f"(+{dominant['seconds_added']:g} s from {dominant['from']:g} to {dominant['to']:g})")
    return "whole krs run (process tree)"


REPORTED_COUNTERS = ("counter.descriptors.total", "counter.provenance.anchors", "counter.provenance.origin_frames",
                     "counter.definition.sentences", "source.bytes")
REPORTED_AXES = ("counter.provenance.anchors", "counter.descriptors.total", "source.bytes")
REPORTED_AXIS_METRICS = ("wall_seconds", "cpu_seconds", "peak_memory_bytes", "llvm_lines.total")


def _number(value: float | None, digits: int = 2) -> str:
    return "-" if value is None else f"{value:.{digits}f}"


def render(ladder: Mapping[str, Any], analysis: Mapping[str, Any], *, all_metrics: bool = False) -> str:
    """A Markdown report of one ladder's fits; flagged slopes first."""

    lines = [f"## {ladder['name']}", ""]
    lines.append(f"{ladder.get('description', '')}".strip())
    lines.append("")
    lines.append(f"Parameter `{ladder.get('param')}`, values measured: "
                 + ", ".join(f"{value:g}" for value in analysis["values"])
                 + f"; flag threshold {analysis['threshold']}.")
    for note in ladder.get("notes", []):
        lines.append(f"- {note}")
    lines.append("")
    flagged = analysis["flagged"]
    if flagged:
        lines.append("Flagged slopes:")
        lines.append("")
        for item in flagged:
            responsible = item.get("responsible")
            lines.append(f"- `{item['metric']}` vs `{item['x']}`: slope {_number(item['slope'])}, "
                         f"top slope {_number(item['top_slope'])}; stage {item['stage']}"
                         + (f"; largest-growth generated group: {responsible}" if responsible else ""))
    else:
        lines.append("No slope exceeds the threshold.")
    dominant = analysis.get("dominant_leaf_span")
    if dominant:
        lines.append("")
        lines.append(f"Largest-growth leaf span between the two largest values: `{dominant['span']}` "
                     f"(+{dominant['seconds_added']:g} s from {dominant['from']:g} to {dominant['to']:g}).")
    lines.append("")
    lines.append("| metric | x | slope | R² | top slope | points | values (min..max) |")
    lines.append("|---|---|---|---|---|---|---|")
    rows = analysis["by_param"] + analysis["by_axis"]
    for row in rows:
        is_flagged = any(f["metric"] == row["metric"] and f["x"] == row["x"] for f in flagged)
        if row["x"] == "param":
            interesting = (row["metric"] in CORE_METRICS or row["metric"] in REPORTED_COUNTERS
                           or (row["metric"].startswith("span.") and not row["below_floor"]))
        else:
            interesting = row["x"] in REPORTED_AXES and row["metric"] in REPORTED_AXIS_METRICS
        if not (all_metrics or interesting or is_flagged):
            continue
        fit = row["fit"] or {}
        values = [value for _, value in row["points"]]
        mark = " (below floor)" if row["below_floor"] else ""
        flag = " **flagged**" if Growth(row["metric"], row["x"], [], Fit(**fit) if fit else None, row["top_slope"],
                                    row["top_sizes"], row["below_floor"]).exceeds(analysis["threshold"]) else ""
        lines.append(f"| `{row['metric']}`{mark}{flag} | {row['x']} | {_number(fit.get('slope'))} | "
                     f"{_number(fit.get('r_squared'), 3)} | {_number(row['top_slope'])} | {len(values)} | "
                     f"{_short(min(values, default=0))}..{_short(max(values, default=0))} |")
    lines.append("")
    return "\n".join(lines)


def _short(value: float) -> str:
    if value >= 1e6:
        return f"{value / 1e6:.1f}M"
    if value >= 1e4:
        return f"{value / 1e3:.0f}k"
    return f"{value:.3g}"
