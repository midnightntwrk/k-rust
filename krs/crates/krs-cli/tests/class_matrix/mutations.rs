//! K5: a package whose only mistake breaks one entry point's header gives exactly one diagnostic,
//! under `krs check --message-format json` and under plain `cargo check`
//! (`krs_test_support::class_matrix::entry_points`).
//!
//! Each mutation is its own package, checked by the `krs` binary this test is built with and by
//! `cargo check`, with the worker's target. The errors and the warnings of each are counted with
//! their codes; a warning counts against the case as an extra diagnostic, since an editor shows it
//! (an `unused_imports` warning that a failed item causes, say). The unmutated base must give
//! none under either.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::sync::Mutex;

use krs_test_support::class_matrix::entry_points::{BASE, mutations};

use crate::pipeline::{Settings, write_package};

/// The diagnostics one tool reported: the codes of its errors and of its warnings.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Counts {
    pub errors: Vec<String>,
    pub warnings: Vec<String>,
}

impl Counts {
    fn spell(&self) -> String {
        let codes = |codes: &[String]| {
            codes
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join(", ")
        };
        format!(
            "{} errors [{}], {} warnings [{}]",
            self.errors.len(),
            codes(&self.errors),
            self.warnings.len(),
            codes(&self.warnings)
        )
    }
}

/// What one package gave under both tools.
#[derive(Clone, Debug)]
pub struct Checked {
    /// The mutation's ID, or `entry/base`.
    pub id: String,
    pub krs: Counts,
    pub cargo: Counts,
}

impl Checked {
    /// Whether each tool reported exactly one error and nothing else.
    #[must_use]
    pub fn conforms(&self) -> bool {
        [&self.krs, &self.cargo]
            .iter()
            .all(|counts| counts.errors.len() == 1 && counts.warnings.is_empty())
    }

    /// The signature `pending.toml` records.
    #[must_use]
    pub fn signature(&self) -> String {
        format!(
            "krs check: {}; cargo check: {}",
            self.krs.spell(),
            self.cargo.spell()
        )
    }
}

/// Check the base and every mutation, `settings.workers` packages at a time.
#[must_use]
pub fn check_all(settings: &Settings) -> Vec<Checked> {
    let mut jobs = mutations()
        .into_iter()
        .map(|mutation| (mutation.id, mutation.source))
        .collect::<Vec<_>>();
    jobs.push(("entry/base".to_owned(), BASE.to_owned()));
    let jobs = Mutex::new(jobs);
    let checked = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for index in 0..settings.workers.max(1) {
            let root = settings.scratch.join(format!("k5-worker-{index}"));
            let (jobs, checked) = (&jobs, &checked);
            scope.spawn(move || {
                loop {
                    let Some((id, source)) =
                        jobs.lock().expect("the job queue is not poisoned").pop()
                    else {
                        break;
                    };
                    let result = check(&root, &id, &source);
                    checked
                        .lock()
                        .expect("the results are not poisoned")
                        .push(result);
                }
            });
        }
    });
    let mut checked = checked.into_inner().expect("the results are not poisoned");
    checked.sort_by(|left, right| left.id.cmp(&right.id));
    checked
}

fn check(root: &Path, id: &str, source: &str) -> Checked {
    let name = format!("krs_entry_{}", id.replace(['/', '-'], "_").to_lowercase());
    let directory = root.join(&name);
    let manifest = write_package(&directory, &name, source);
    let target = root.join("target");
    let krs = Command::new(env!("CARGO_BIN_EXE_krs"))
        .args([
            "check",
            "--message-format",
            "json",
            "--no-reuse",
            "--manifest-path",
        ])
        .arg(&manifest)
        .args(["--package", &name, "--definition", "main"])
        .env("CARGO_TARGET_DIR", &target)
        .env("RUSTC_WRAPPER", "")
        .env("NO_COLOR", "1")
        .output()
        .expect("krs runs");
    let cargo = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into()))
        .args(["check", "--message-format", "json", "--manifest-path"])
        .arg(&manifest)
        .env("CARGO_TARGET_DIR", &target)
        .env("RUSTC_WRAPPER", "")
        .output()
        .expect("cargo runs");
    let checked = Checked {
        id: id.to_owned(),
        krs: krs_counts(&String::from_utf8_lossy(&krs.stderr)),
        cargo: cargo_counts(&String::from_utf8_lossy(&cargo.stdout), &manifest),
    };
    let _ = fs::remove_dir_all(&directory);
    checked
}

/// The diagnostics of `krs --message-format json`: one envelope per JSON line, and one prose line
/// (`krs: CODE: message`, `warning:` before a warning's code) per unlocated diagnostic.
fn krs_counts(stderr: &str) -> Counts {
    let mut counts = Counts::default();
    for line in stderr.lines() {
        if let Ok(envelope) = serde_json::from_str::<serde_json::Value>(line) {
            let code = envelope["code"].as_str().unwrap_or("uncoded").to_owned();
            match envelope["severity"].as_str() {
                Some("warning") => counts.warnings.push(code),
                _ => counts.errors.push(code),
            }
        } else if let Some(prose) = line.strip_prefix("krs: ") {
            let (warning, prose) = prose
                .strip_prefix("warning: ")
                .map_or((false, prose), |rest| (true, rest));
            let code = prose
                .split_once(": ")
                .map_or("uncoded", |(code, _)| code)
                .to_owned();
            if warning {
                counts.warnings.push(code);
            } else {
                counts.errors.push(code);
            }
        }
    }
    counts
}

/// The diagnostics plain `cargo check` reports for the package itself: its compiler messages,
/// coded by rustc's code or lint, or by the KRS code a macro's message is tagged with.
fn cargo_counts(stdout: &str, manifest: &Path) -> Counts {
    let mut counts = Counts::default();
    for line in stdout.lines() {
        let Ok(message) = serde_json::from_str::<serde_json::Value>(line) else {
            continue;
        };
        if message["reason"] != "compiler-message"
            || message["manifest_path"].as_str() != manifest.to_str()
        {
            continue;
        }
        let diagnostic = &message["message"];
        let text = diagnostic["message"].as_str().unwrap_or_default();
        let code = diagnostic["code"]["code"].as_str().map_or_else(
            || {
                text.strip_prefix('[')
                    .and_then(|rest| rest.split_once(']'))
                    .map_or("uncoded", |(code, _)| code)
                    .to_owned()
            },
            str::to_owned,
        );
        match diagnostic["level"].as_str() {
            Some("error") => counts.errors.push(code),
            Some("warning") => counts.warnings.push(code),
            _ => {}
        }
    }
    counts
}
