//! The facade's pattern result forms (`Backend::execute_kore` and the others) against its
//! `serde_json::Value` forms: for one request, each pair serializes to the same JSON, each run on
//! a fresh backend.
//!
//! Test binaries include this file with
//! `#[path = "support/pattern_results.rs"] mod pattern_results;`.

use k_rust::backend::{
    Backend, ExecuteRequest, ObservedRequest, SearchPatternRequest, SearchRequest,
};
use serde_json::{Map, Value};

/// `serde_json::to_value` and `serde_json::to_string` of `result`, which the facade returned.
fn json<T: serde::Serialize, E: std::fmt::Display>(
    form: &str,
    result: Result<T, E>,
) -> (Value, String) {
    let result = result.unwrap_or_else(|error| panic!("{form}: {error}"));
    let value = serde_json::to_value(&result).unwrap_or_else(|error| panic!("{form}: {error}"));
    let text = serde_json::to_string(&result).unwrap_or_else(|error| panic!("{form}: {error}"));
    (value, text)
}

/// Assert that `$kore` and `$value`, called on fresh backends with `$request`, serialize alike,
/// as a JSON value and as JSON text, and push the JSON onto `$seen`.
macro_rules! alike {
    ($fresh:expr, $seen:expr, $value:ident, $kore:ident, $request:expr) => {{
        let (expected, expected_text) = json(stringify!($value), $fresh().$value($request));
        let (actual, actual_text) = json(stringify!($kore), $fresh().$kore($request));
        assert_eq!(actual, expected, "{}", stringify!($kore));
        assert_eq!(actual_text, expected_text, "{}", stringify!($kore));
        $seen.push(expected);
    }};
}

/// Assert that `execute_kore` and `execute_observed_kore` (observing every rule) serialize as
/// `execute` and `execute_observed` for `request`; the four results' JSON.
#[allow(dead_code)]
pub fn executions_alike(fresh: impl Fn() -> Backend, request: &ExecuteRequest) -> Vec<Value> {
    let observed = || ObservedRequest {
        request: request.clone(),
        rules: None,
    };
    let mut seen = Vec::new();
    alike!(fresh, seen, execute, execute_kore, request.clone());
    alike!(
        fresh,
        seen,
        execute_observed,
        execute_observed_kore,
        observed()
    );
    seen
}

/// Assert that `search_kore`, `search_paths_kore` and their observed forms (observing every
/// rule) serialize as their `Value` forms for `request`; the responses' JSON.
#[allow(dead_code)]
pub fn searches_alike(fresh: impl Fn() -> Backend, request: &SearchRequest) -> Vec<Value> {
    let observed = || ObservedRequest {
        request: request.clone(),
        rules: None,
    };
    let mut seen = Vec::new();
    alike!(fresh, seen, search, search_kore, request.clone());
    alike!(
        fresh,
        seen,
        search_observed,
        search_observed_kore,
        observed()
    );
    alike!(
        fresh,
        seen,
        search_paths,
        search_paths_kore,
        request.clone()
    );
    alike!(
        fresh,
        seen,
        search_paths_observed,
        search_paths_observed_kore,
        observed()
    );
    seen
}

/// Assert that `search_pattern_kore`, `search_pattern_paths_kore` and their observed forms
/// (observing every rule) serialize as their `Value` forms for `request`; the responses' JSON.
#[allow(dead_code)]
pub fn pattern_searches_alike(
    fresh: impl Fn() -> Backend,
    request: &SearchPatternRequest,
) -> Vec<Value> {
    let observed = || ObservedRequest {
        request: request.clone(),
        rules: None,
    };
    let mut seen = Vec::new();
    alike!(
        fresh,
        seen,
        search_pattern,
        search_pattern_kore,
        request.clone()
    );
    alike!(
        fresh,
        seen,
        search_pattern_observed,
        search_pattern_observed_kore,
        observed()
    );
    alike!(
        fresh,
        seen,
        search_pattern_paths,
        search_pattern_paths_kore,
        request.clone()
    );
    alike!(
        fresh,
        seen,
        search_pattern_paths_observed,
        search_pattern_paths_observed_kore,
        observed()
    );
    seen
}

/// Whether `member` is a value other than `null`, `false`, `0`, an empty array or an empty
/// object.
fn shown(member: &Value) -> bool {
    match member {
        Value::Null | Value::Bool(false) => false,
        Value::Number(number) => number.as_f64() != Some(0.0),
        Value::Array(items) => !items.is_empty(),
        Value::Object(members) => !members.is_empty(),
        Value::Bool(true) | Value::String(_) => true,
    }
}

/// Whether some object in `values`, at any depth, satisfies `holds`.
fn some_object(values: &[Value], holds: impl Fn(&Map<String, Value>) -> bool) -> bool {
    let mut work: Vec<&Value> = values.iter().collect();
    while let Some(value) = work.pop() {
        match value {
            Value::Object(members) => {
                if holds(members) {
                    return true;
                }
                work.extend(members.values());
            }
            Value::Array(items) => work.extend(items),
            Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => {}
        }
    }
    false
}

/// Whether some object in `values`, at any depth, has the member `key` with a value other than
/// `null`, `false`, `0`, an empty array or an empty object.
/// A fixture checks its own results with it, so that what it is meant to show is shown by it
/// and not by another fixture's results.
#[allow(dead_code)]
pub fn shows(values: &[Value], key: &str) -> bool {
    some_object(values, |members| members.get(key).is_some_and(shown))
}

/// Whether some leaf in `values` whose `reason` is `reason` shows `key`, as [`shows`] reads it.
#[allow(dead_code)]
pub fn leaf_shows(values: &[Value], reason: &str, key: &str) -> bool {
    some_object(values, |members| {
        members.get("reason").and_then(Value::as_str) == Some(reason)
            && members.get(key).is_some_and(shown)
    })
}
