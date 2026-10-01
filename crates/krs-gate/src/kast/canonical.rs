use serde_json::Value;

/// Serialize JSON with sorted Unicode keys, compact separators, and raw non-ASCII text.
#[must_use]
pub fn canonical_json(value: &Value) -> String {
    render(value)
}

fn render(value: &Value) -> String {
    match value {
        Value::Array(items) => format!(
            "[{}]",
            items.iter().map(render).collect::<Vec<_>>().join(",")
        ),
        Value::Object(fields) => {
            let mut fields = fields.iter().collect::<Vec<_>>();
            fields.sort_by_key(|(left, _)| *left);
            format!(
                "{{{}}}",
                fields
                    .into_iter()
                    .map(|(key, child)| format!(
                        "{}:{}",
                        serde_json::to_string(key).expect("JSON keys serialize"),
                        render(child)
                    ))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        }
        Value::Number(number) if number.is_f64() => python_float(&number.to_string()),
        _ => serde_json::to_string(value).expect("JSON values serialize"),
    }
}

fn python_float(spelling: &str) -> String {
    let (sign, positive) = spelling
        .strip_prefix('-')
        .map_or(("", spelling), |value| ("-", value));
    let (mantissa, exponent) =
        positive
            .split_once('e')
            .map_or((positive, 0), |(mantissa, exponent)| {
                (
                    mantissa,
                    exponent.parse::<i32>().expect("JSON float exponent"),
                )
            });
    let decimal = mantissa.find('.').unwrap_or(mantissa.len());
    let digits = mantissa.replace('.', "");
    let leading = digits.bytes().take_while(|digit| *digit == b'0').count();
    if leading == digits.len() {
        return format!("{sign}0.0");
    }
    let significant = digits[leading..].trim_end_matches('0');
    let power = i32::try_from(decimal).expect("float mantissa length")
        - i32::try_from(leading).expect("float leading zero count")
        - 1
        + exponent;
    if !(-4..16).contains(&power) {
        let fraction = if significant.len() > 1 {
            format!(".{}", &significant[1..])
        } else {
            String::new()
        };
        format!(
            "{sign}{}{fraction}e{}{:02}",
            &significant[..1],
            if power < 0 { "-" } else { "+" },
            power.abs()
        )
    } else if power < 0 {
        format!(
            "{sign}0.{}{}",
            "0".repeat(usize::try_from(-power - 1).expect("nonnegative zero count")),
            significant
        )
    } else {
        let decimal = usize::try_from(power + 1).expect("nonnegative decimal position");
        if decimal >= significant.len() {
            format!(
                "{sign}{significant}{}.0",
                "0".repeat(decimal - significant.len())
            )
        } else {
            format!(
                "{sign}{}.{}",
                &significant[..decimal],
                &significant[decimal..]
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::canonical_json;
    use serde_json::json;

    #[test]
    fn python_canonical_vectors() {
        for (value, expected) in [
            (
                json!([1e-7, 1e-5, 0.0001, 1e15, 1e16, -0.0]),
                "[1e-07,1e-05,0.0001,1000000000000000.0,1e+16,-0.0]",
            ),
            (
                json!([1e-7, 1e-5, 1e16, 1.0, -0.0]),
                "[1e-07,1e-05,1e+16,1.0,-0.0]",
            ),
            (json!({"z":1,"a":true}), "{\"a\":true,\"z\":1}"),
            (
                json!(["é", "😀", "\u{2028}", "\u{007f}"]),
                "[\"é\",\"😀\",\"\u{2028}\",\"\u{007f}\"]",
            ),
            (
                json!("\u{0000}\u{0001}\u{0008}\u{000c}\n\r\t\"\\/"),
                "\"\\u0000\\u0001\\b\\f\\n\\r\\t\\\"\\\\/\"",
            ),
            (
                json!({"😀":0,"\u{e000}":1,"a":2}),
                "{\"a\":2,\"\u{e000}\":1,\"😀\":0}",
            ),
        ] {
            assert_eq!(canonical_json(&value), expected);
        }
    }
}
