//! The output check of a run (`check` in the registry).

use std::collections::BTreeMap;
use std::fs::File;
use std::io::Read;
use std::path::Path;

use crate::expand::{Vars, evaluate};
use crate::registry::Check;

/// Binds `${expect}` from `check.expect` or `check.expect_out`.
pub fn bind_expect(
    check: &Check,
    vars: &mut Vars,
    params: &BTreeMap<String, i64>,
) -> Result<(), String> {
    if let Some(expression) = &check.expect {
        let value = evaluate(&vars.expand(expression)?, params)?;
        vars.set("expect", value.to_string());
    } else if let Some(path) = &check.expect_out {
        let path = vars.expand(path)?;
        let text = std::fs::read_to_string(&path)
            .map_err(|error| format!("cannot read expect_out {path}: {error}"))?;
        let value = equals_integer(&text)
            .ok_or_else(|| format!("{path} binds no `#Equals <int>` value"))?;
        vars.set("expect", value);
    }
    Ok(())
}

/// The integer after the first `#Equals` of K's `V:K #Equals <int> ~> .K` output.
fn equals_integer(text: &str) -> Option<String> {
    let after = &text[text.find("#Equals")? + "#Equals".len()..];
    let digits: String = after
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '-')
        .collect();
    (!digits.is_empty()).then_some(digits)
}

/// Streams `path` and reports which of `needles` occur, optionally with whitespace removed.
fn find_all(path: &Path, needles: &[String], squeeze: bool) -> Result<Vec<bool>, String> {
    let mut found = vec![false; needles.len()];
    if needles.is_empty() {
        return Ok(found);
    }
    let overlap = needles.iter().map(String::len).max().unwrap_or(0);
    let mut file =
        File::open(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let mut window: Vec<u8> = Vec::new();
    let mut chunk = vec![0u8; 1 << 20];
    loop {
        let read = file
            .read(&mut chunk)
            .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        if squeeze {
            window.extend(chunk[..read].iter().filter(|b| !b.is_ascii_whitespace()));
        } else {
            window.extend_from_slice(&chunk[..read]);
        }
        for (index, needle) in needles.iter().enumerate() {
            if !found[index] && contains(&window, needle.as_bytes()) {
                found[index] = true;
            }
        }
        if window.len() > overlap {
            window.drain(..window.len() - overlap);
        }
    }
    Ok(found)
}

fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    needle.is_empty() || haystack.windows(needle.len()).any(|w| w == needle)
}

/// Checks a finished run; the error names the first failed expectation.
pub fn verify(
    check: &Check,
    vars: &Vars,
    exit_code: i32,
    stdout: Option<&Path>,
) -> Result<(), String> {
    let expected_exit = check.exit.unwrap_or(0);
    if exit_code != expected_exit {
        return Err(format!("exit status {exit_code}, expected {expected_exit}"));
    }
    if let Some(stdout) = stdout {
        let plain = vars.expand_all(&check.stdout)?;
        for (needle, found) in plain.iter().zip(find_all(stdout, &plain, false)?) {
            if !found {
                return Err(format!("standard output lacks {needle:?}"));
            }
        }
        let squeezed: Vec<String> = vars
            .expand_all(&check.stdout_squeezed)?
            .into_iter()
            .map(|s| s.chars().filter(|c| !c.is_ascii_whitespace()).collect())
            .collect();
        for (needle, found) in squeezed.iter().zip(find_all(stdout, &squeezed, true)?) {
            if !found {
                return Err(format!(
                    "standard output (whitespace removed) lacks {needle:?}"
                ));
            }
        }
        let absent = vars.expand_all(&check.stdout_absent)?;
        for (needle, found) in absent.iter().zip(find_all(stdout, &absent, false)?) {
            if found {
                return Err(format!("standard output contains {needle:?}"));
            }
        }
    }
    for file in vars.expand_all(&check.files)? {
        let non_empty = std::fs::metadata(&file).is_ok_and(|m| m.len() > 0);
        if !non_empty {
            return Err(format!("{file} is missing or empty"));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_equals_integer() {
        assert_eq!(
            equals_integer("V:K #Equals 4 ~> .K\n").as_deref(),
            Some("4")
        );
    }

    #[test]
    fn finds_needles_across_chunk_boundaries() {
        let dir = std::env::temp_dir().join(format!("kbench-check-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("out");
        let mut text = "x".repeat((1 << 20) - 3);
        text.push_str("needle here");
        std::fs::write(&path, &text).unwrap();
        let found = find_all(&path, &["needle".to_owned(), "absent".to_owned()], false).unwrap();
        assert_eq!(found, vec![true, false]);
        let squeezed = find_all(&path, &["needlehere".to_owned()], true).unwrap();
        assert_eq!(squeezed, vec![true]);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
