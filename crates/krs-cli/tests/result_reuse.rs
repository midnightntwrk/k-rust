//! Command result reuse across repeated CLI invocations.

use std::collections::BTreeSet;
use std::fs::{self, File, FileTimes};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, UNIX_EPOCH};

use krs_test_support::{TempDir, fixture_target, krs_command, temp_dir};

const FOO_BAR: &str = include_str!("fixtures/foo-bar/src/lib.rs");
const INVALID_NATIVE: &str = include_str!("fixtures/nested-function-pattern/src/lib.rs");

struct Fixture {
    root: TempDir,
    manifest: PathBuf,
    target: PathBuf,
    executable: PathBuf,
    next: AtomicU64,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let root = temp_dir();
        let project = root.path().join("language");
        fs::create_dir_all(project.join("src")).unwrap();
        fs::write(project.join("src/lib.rs"), source).unwrap();
        let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../krs")
            .canonicalize()
            .unwrap();
        let krs_literal = serde_json::to_string(krs.to_str().unwrap()).unwrap();
        let manifest = project.join("Cargo.toml");
        fs::write(
            &manifest,
            format!(
                "[package]\nname = \"krs-result-reuse-fixture\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nkrs = {{ path = {krs_literal} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-RESULT-REUSE\"\n\n[package.metadata.krs.definitions.main]\nroot = \"crate\"\nsyntax-root = \"crate\"\n\n[workspace]\n"
            ),
        )
        .unwrap();
        let executable = root.path().join("krs");
        copy_executable(Path::new(env!("CARGO_BIN_EXE_krs")), &executable);
        Self {
            target: fixture_target(&manifest, Some(root.path())),
            root,
            manifest,
            executable,
            next: AtomicU64::new(0),
        }
    }

    fn run(
        &self,
        kind: &str,
        backend: &str,
        output: Option<&Path>,
        options: &[&str],
        no_reuse_env: bool,
    ) -> Run {
        let sequence = self.next.fetch_add(1, Ordering::Relaxed);
        let counters_path = self.root.path().join(format!("counters-{sequence}.json"));
        let timings_path = self.root.path().join(format!("timings-{sequence}.json"));
        let mut command = krs_command!(&self.executable);
        command
            .arg(kind)
            .args(options)
            .args(["--manifest-path"])
            .arg(&self.manifest)
            .args([
                "--package",
                "krs-result-reuse-fixture",
                "--definition",
                "main",
                "--backend",
                backend,
                "--counters",
            ])
            .arg(&counters_path)
            .arg("--timings")
            .arg(&timings_path)
            .env("CARGO_TARGET_DIR", &self.target)
            .env("CARGO_NET_OFFLINE", "true")
            .env("RUSTUP_TOOLCHAIN", "stable")
            .env_remove("KRS_NO_REUSE");
        if let Some(output) = output {
            command.arg("--output").arg(output);
        }
        if no_reuse_env {
            command.env("KRS_NO_REUSE", "1");
        }
        let output = command.output().unwrap();
        let counters = read_json(&counters_path, &output);
        let timings = read_json(&timings_path, &output);
        Run {
            output,
            counters,
            timings,
        }
    }

    fn source(&self) -> PathBuf {
        self.manifest.parent().unwrap().join("src/lib.rs")
    }

    fn cache_file_names(&self) -> BTreeSet<String> {
        fs::read_dir(self.target.join("krs/collectors"))
            .unwrap()
            .flat_map(|entry| fs::read_dir(entry.unwrap().path()).unwrap())
            .map(|entry| entry.unwrap().file_name().to_string_lossy().into_owned())
            .filter(|name| name.starts_with("krs-result-"))
            .collect()
    }
}

struct Run {
    output: Output,
    counters: serde_json::Value,
    timings: serde_json::Value,
}

impl Run {
    fn assert_reused(&self, expected: u64) {
        assert!(
            self.output.status.success(),
            "{}",
            String::from_utf8_lossy(&self.output.stderr)
        );
        assert_eq!(self.counters["status"], "ok");
        assert_eq!(
            self.counters["counters"]["result.reused"],
            expected,
            "{}",
            String::from_utf8_lossy(&self.output.stderr)
        );
        let spans = self.timings["spans"].as_array().unwrap();
        let has = |id: &str| spans.iter().any(|span| span["id"] == id);
        if expected == 1 {
            let ids = spans
                .iter()
                .map(|span| {
                    (
                        span["id"].as_str().unwrap(),
                        span["depth"].as_u64().unwrap(),
                    )
                })
                .collect::<Vec<_>>();
            assert_eq!(
                ids,
                [
                    ("cargo.metadata.input", 0),
                    ("host.discover", 0),
                    ("cargo.metadata.runtime", 0),
                    ("collector.plan", 0),
                    ("collector.generate", 0),
                    ("collector.build", 0),
                    ("result.reuse", 0),
                ]
            );
        } else {
            assert!(has("collector.run"), "{}", self.timings);
        }
    }
}

/// Copy an executable without opening it for writing in this process.
///
/// Tests in this binary spawn processes concurrently.
/// A child forked by one test inherits every descriptor open in the process until it execs,
/// and executing a file while any process holds it open for writing fails with `ETXTBSY`.
fn copy_executable(from: &Path, to: &Path) {
    let status = Command::new("cp").arg(from).arg(to).status().unwrap();
    assert!(
        status.success(),
        "cp {} {}: {status}",
        from.display(),
        to.display()
    );
}

fn read_json(path: &Path, output: &Output) -> serde_json::Value {
    let bytes = fs::read(path).unwrap_or_else(|error| {
        panic!(
            "{}: {error}\nstatus: {}\nstderr:\n{}",
            path.display(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        )
    });
    serde_json::from_slice(&bytes).unwrap()
}

fn artifact_bytes(directory: &Path) -> Vec<(String, Vec<u8>)> {
    let mut files = fs::read_dir(directory)
        .unwrap()
        .map(|entry| {
            let entry = entry.unwrap();
            (
                entry.file_name().to_string_lossy().into_owned(),
                fs::read(entry.path()).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    files.sort_by(|left, right| left.0.cmp(&right.0));
    files
}

#[test]
fn hit_skips_collector_and_restores_only_changed_outputs() {
    let fixture = Fixture::new(FOO_BAR);
    let first_directory = fixture.root.path().join("first");
    let first = fixture.run("emit-k", "llvm", Some(&first_directory), &[], false);
    first.assert_reused(0);
    let expected = artifact_bytes(&first_directory);

    let second_directory = fixture.root.path().join("second");
    let second = fixture.run("emit-k", "llvm", Some(&second_directory), &[], false);
    second.assert_reused(1);
    assert_eq!(second.output.stdout, first.output.stdout);
    assert_eq!(artifact_bytes(&second_directory), expected);

    let other_backend_directory = fixture.root.path().join("other-backend");
    let other_backend = fixture.run(
        "emit-k",
        "haskell",
        Some(&other_backend_directory),
        &[],
        false,
    );
    other_backend.assert_reused(1);
    assert_eq!(artifact_bytes(&other_backend_directory), expected);
    assert_eq!(
        fixture.cache_file_names(),
        ["krs-result-emit-k.bin".to_owned()].into()
    );

    let unchanged = second_directory.join("semantic-ir.json");
    let old_time = UNIX_EPOCH + Duration::from_secs(12_345);
    File::options()
        .write(true)
        .open(&unchanged)
        .unwrap()
        .set_times(FileTimes::new().set_modified(old_time))
        .unwrap();
    fs::remove_file(second_directory.join("definition.k")).unwrap();
    fs::write(second_directory.join("symbols.json"), b"modified").unwrap();
    let third = fixture.run("emit-k", "llvm", Some(&second_directory), &[], false);
    third.assert_reused(1);
    assert_eq!(third.output.stdout, first.output.stdout);
    assert_eq!(artifact_bytes(&second_directory), expected);
    assert_eq!(
        fs::metadata(unchanged).unwrap().modified().unwrap(),
        old_time
    );
}

#[test]
fn source_request_and_executable_changes_miss_and_escape_hatches_recompute() {
    let fixture = Fixture::new(FOO_BAR);
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(0);
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(1);

    let rule_edit = FOO_BAR.replace("    Bar\n}", "    Foo\n}");
    assert_ne!(rule_edit, FOO_BAR);
    fs::write(fixture.source(), &rule_edit).unwrap();
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(0);

    let comment_edit = format!("// Shifts authored source positions.\n{rule_edit}");
    fs::write(fixture.source(), &comment_edit).unwrap();
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(0);

    fs::write(
        fixture.source(),
        format!("{comment_edit}\n// Read at collection.\n"),
    )
    .unwrap();
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(0);
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(1);

    fixture
        .run("check", "haskell", None, &[], false)
        .assert_reused(0);
    fixture
        .run("check", "haskell", None, &[], false)
        .assert_reused(1);
    let cache_files = fixture.cache_file_names();
    assert!(cache_files.contains("krs-result-check-llvm.bin"));
    assert!(cache_files.contains("krs-result-check-haskell.bin"));
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(1);
    let emitted = fixture.root.path().join("emitted");
    fixture
        .run("emit-k", "llvm", Some(&emitted), &[], false)
        .assert_reused(0);
    fixture
        .run("emit-k", "llvm", Some(&emitted), &[], false)
        .assert_reused(1);
    let native = fixture.root.path().join("native");
    let build = fixture.run("build", "llvm", Some(&native), &[], false);
    build.assert_reused(0);
    let native_bytes = artifact_bytes(&native);
    let reused_build = fixture.run("build", "llvm", Some(&native), &[], false);
    reused_build.assert_reused(1);
    assert_eq!(reused_build.output.stdout, build.output.stdout);
    assert_eq!(artifact_bytes(&native), native_bytes);
    assert!(
        fixture
            .cache_file_names()
            .contains("krs-result-build-llvm.bin")
    );

    fixture
        .run("check", "llvm", None, &["--no-reuse"], false)
        .assert_reused(0);
    fixture
        .run("check", "llvm", None, &[], true)
        .assert_reused(0);
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(1);

    // Explicit times need no write access.
    // A writable descriptor could leak into a child that another test is forking,
    // and the next run of this executable would then fail (see `copy_executable`).
    File::open(&fixture.executable)
        .unwrap()
        .set_times(FileTimes::new().set_modified(UNIX_EPOCH + Duration::from_secs(12_345)))
        .unwrap();
    fixture
        .run("check", "llvm", None, &[], false)
        .assert_reused(0);
}

#[test]
fn failed_native_compilation_is_never_reused() {
    let fixture = Fixture::new(INVALID_NATIVE);
    let native = fixture.root.path().join("native");
    for _ in 0..2 {
        let run = fixture.run("build", "llvm", Some(&native), &[], false);
        let context = format!(
            "status: {}\nstderr:\n{}\ncounters: {}\ntimings: {}",
            run.output.status,
            String::from_utf8_lossy(&run.output.stderr),
            run.counters,
            run.timings
        );
        assert!(!run.output.status.success(), "{context}");
        assert_eq!(run.counters["status"], "failed", "{context}");
        assert_eq!(run.counters["counters"]["result.reused"], 0, "{context}");
        assert_eq!(run.timings["failed_span"], "native.compile", "{context}");
        let spans = run.timings["spans"].as_array().unwrap();
        assert!(
            spans.iter().any(|span| span["id"] == "collector.run"),
            "{context}"
        );
        assert!(!native.exists(), "{context}");
    }
}
