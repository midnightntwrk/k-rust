//! Metrics: values an implementation states of its run (`metrics`, `kink-implementation/3`),
//! measured under a `metric` projection (projections PJ-21).
//!
//! A metric is a count the implementation makes of its run on one request: bytes allocated or
//! peak live bytes from a counting allocator, instructions executed. Where the implementation
//! counts it deterministically it is a fact of the binary and the request, so it is cached with
//! the answer and judged against a baseline a user accepted, a snapshot ([`baseline`],
//! `crate::snapshot`): `improved`, `regressed` or `stayed` in the projection's [`Direction`],
//! with the change. The lock records the verdict, never the value: a metric's history is its
//! baselines' commit history and each run's compare document. A metric the flow declares
//! `host_dependent` (wall time, resident memory) is a fact of the host as well: it is reported
//! only.
//!
//! A value is a non-negative integer no greater than [`METRIC_MAX`], so that every change of one
//! value from another, and its sign, is exact as an `i64`.

use crate::manifest::{Direction, MetricSection};
use crate::snapshot::SnapshotValue;
use serde_json::{Map, Value, json};

/// The greatest value a metric may state: `i64::MAX`.
pub const METRIC_MAX: u64 = i64::MAX.unsigned_abs();

/// Read an answer's `metrics`: a JSON object of metric names, each nonempty, to values
/// ([`value_of`]).
///
/// # Errors
///
/// Why `metrics` is no such object, naming the metric.
pub fn read_metrics(metrics: Value) -> Result<Map<String, Value>, String> {
    let Value::Object(metrics) = metrics else {
        return Err("`metrics` is not a JSON object".to_owned());
    };
    for (name, value) in &metrics {
        if name.trim().is_empty() {
            return Err("`metrics` names a metric by a blank name".to_owned());
        }
        value_of(value).map_err(|why| format!("`metrics.{name}` {why}"))?;
    }
    Ok(metrics)
}

/// A metric's value as a JSON document states it: an integer from 0 to [`METRIC_MAX`].
///
/// # Errors
///
/// Why `value` is no such integer.
pub fn value_of(value: &Value) -> Result<u64, String> {
    value
        .as_u64()
        .filter(|value| *value <= METRIC_MAX)
        .ok_or_else(|| {
            format!(
                "is {value}, not a metric's value: a non-negative integer no greater than \
                 {METRIC_MAX}"
            )
        })
}

/// The value of `metric` an answer's `metrics` states, if it states one.
#[must_use]
pub fn stated(metrics: Option<&Map<String, Value>>, metric: &str) -> Option<u64> {
    metrics
        .and_then(|metrics| metrics.get(metric))
        .and_then(|value| value_of(value).ok())
}

/// The baseline file's value of `value` measured for `metric`: `{metric, value}`.
#[must_use]
pub fn baseline(metric: &str, value: u64) -> SnapshotValue {
    SnapshotValue(json!({"metric": metric, "value": value}))
}

/// The value a baseline file holds for `metric`.
///
/// # Errors
///
/// Why the file's document is no baseline of `metric` ([`baseline`]'s shape).
pub fn baseline_of(accepted: &SnapshotValue, metric: &str) -> Result<u64, String> {
    let Value::Object(members) = &accepted.0 else {
        return Err(format!(
            "it holds no baseline: expected {{\"metric\": {metric:?}, \"value\": N}}"
        ));
    };
    if let Some(key) = members
        .keys()
        .find(|key| !matches!(key.as_str(), "metric" | "value"))
    {
        return Err(format!(
            "it holds the key `{key}`; a baseline holds `metric` and `value` only"
        ));
    }
    if members.get("metric").and_then(Value::as_str) != Some(metric) {
        return Err(format!(
            "it is no baseline of the metric `{metric}` (its `metric` is {})",
            members.get("metric").unwrap_or(&Value::Null)
        ));
    }
    value_of(members.get("value").unwrap_or(&Value::Null)).map_err(|why| format!("its value {why}"))
}

/// A value judged against its baseline.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Judged {
    /// `improved`, `regressed` or `stayed`.
    pub verdict: &'static str,
    /// `value - baseline`.
    pub change: i64,
    /// Whether a regression exceeds the projection's `max_regression`; `None` without one.
    pub exceeded: Option<bool>,
}

/// Judge `value` against `baseline` under `metric`: better in its direction is `improved`,
/// worse `regressed` (beyond `max_regression`, where it has one, `exceeded`), equal `stayed`.
#[must_use]
pub fn judge(metric: &MetricSection, value: u64, baseline: u64) -> Judged {
    let change = i64::try_from(value).unwrap_or(i64::MAX) - i64::try_from(baseline).unwrap_or(0);
    let regression = match metric.direction {
        Direction::Lower => value.saturating_sub(baseline),
        Direction::Higher => baseline.saturating_sub(value),
    };
    let verdict = if value == baseline {
        "stayed"
    } else if regression > 0 {
        "regressed"
    } else {
        "improved"
    };
    Judged {
        verdict,
        change,
        exceeded: metric
            .max_regression
            .map(|gate| regression > 0 && gate.exceeded(regression, baseline)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::MaxRegression;

    fn metric(direction: Direction, max_regression: Option<MaxRegression>) -> MetricSection {
        MetricSection {
            name: "bytes".into(),
            direction,
            max_regression,
            host_dependent: false,
        }
    }

    /// `metrics` holds counts: non-negative integers within `i64`, by nonblank names.
    #[test]
    fn a_metric_is_a_count() {
        let read = read_metrics(json!({"bytes": 0, "steps": METRIC_MAX})).unwrap();
        assert_eq!(stated(Some(&read), "steps"), Some(METRIC_MAX));
        assert_eq!(stated(Some(&read), "other"), None);
        for (metrics, why) in [
            (json!([1]), "`metrics` is not a JSON object"),
            (json!({"": 1}), "blank name"),
            (
                json!({"bytes": -1}),
                "`metrics.bytes` is -1, not a metric's value",
            ),
            (
                json!({"bytes": 1.0}),
                "`metrics.bytes` is 1.0, not a metric's value",
            ),
            (json!({"bytes": "1"}), "not a metric's value"),
            (json!({"bytes": METRIC_MAX + 1}), "not a metric's value"),
        ] {
            let error = read_metrics(metrics.clone()).unwrap_err();
            assert!(error.contains(why), "{metrics}: {error}");
        }
    }

    /// A baseline is `{metric, value}` of the projection's metric.
    #[test]
    fn a_baseline_names_its_metric() {
        let file = baseline("bytes", 12);
        assert_eq!(
            file.render(),
            "{\n  \"metric\": \"bytes\",\n  \"value\": 12\n}\n"
        );
        assert_eq!(baseline_of(&file, "bytes"), Ok(12));
        assert!(
            baseline_of(&file, "steps")
                .unwrap_err()
                .contains("no baseline of the metric `steps`")
        );
        for (document, why) in [
            (json!(12), "it holds no baseline"),
            (
                json!({"metric": "bytes", "value": 1, "x": 0}),
                "the key `x`",
            ),
            (json!({"metric": "bytes", "value": -2}), "its value is -2"),
            (json!({"metric": "bytes"}), "its value is null"),
        ] {
            let error = baseline_of(&SnapshotValue(document.clone()), "bytes").unwrap_err();
            assert!(error.contains(why), "{document}: {error}");
        }
    }

    /// The verdict follows the direction; a gate marks a regression beyond it, in integers.
    #[test]
    fn a_value_is_judged_against_its_baseline_in_its_direction() {
        let lower = metric(Direction::Lower, None);
        assert_eq!(
            judge(&lower, 90, 100),
            Judged {
                verdict: "improved",
                change: -10,
                exceeded: None
            }
        );
        assert_eq!(judge(&lower, 110, 100).verdict, "regressed");
        assert_eq!(judge(&lower, 110, 100).change, 10);
        assert_eq!(judge(&lower, 100, 100).verdict, "stayed");
        let higher = metric(Direction::Higher, None);
        assert_eq!(judge(&higher, 90, 100).verdict, "regressed");
        assert_eq!(judge(&higher, 110, 100).verdict, "improved");
        let extreme = judge(&lower, 0, METRIC_MAX);
        assert_eq!(extreme.change, -i64::MAX);
        let absolute = metric(Direction::Lower, Some(MaxRegression::Absolute(10)));
        assert_eq!(judge(&absolute, 110, 100).exceeded, Some(false));
        assert_eq!(judge(&absolute, 111, 100).exceeded, Some(true));
        assert_eq!(judge(&absolute, 50, 100).exceeded, Some(false));
        let percent = metric(Direction::Higher, Some(MaxRegression::Percent(5)));
        assert_eq!(judge(&percent, 95, 100).exceeded, Some(false));
        assert_eq!(judge(&percent, 94, 100).exceeded, Some(true));
        // A baseline of 0 lets no regression through a percentage.
        let zero = metric(Direction::Lower, Some(MaxRegression::Percent(50)));
        assert_eq!(judge(&zero, 1, 0).exceeded, Some(true));
        assert_eq!(judge(&zero, 0, 0).exceeded, Some(false));
    }
}
