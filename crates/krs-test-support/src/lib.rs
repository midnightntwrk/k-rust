//! Shared assertions and fixture support for KRS tests.
//!
//! Checked-in fixtures must use [`fixture_target`], a stable directory keyed by the absolute manifest path.
//! Generated fixtures must use [`shared_fixture_target`], a guarded per-process target shared by overlapping tests.
//! A test of fresh-target behavior must use its own guarded scratch target.
//! Fixture builds must apply [`fixture_build_env`] unless the test observes rustc invocations through its own wrapper.

use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::{Arc, Mutex, OnceLock, Weak};

mod compile_fixtures;
pub use compile_fixtures::{Expectation, check_compile_fixtures};

/// Compares `actual` with the versioned pin file `tests_dir/file`, byte for byte.
///
/// A missing file is written only while `UPDATE_EXPECT=1`; an existing file is compared even
/// while recording and never overwritten, because a released version's file is immutable.
/// `bump` names the version constants that must advance before a changed shape gets a new file.
///
/// # Panics
///
/// Panics if the file differs from `actual`, is missing outside recording, or cannot be read or written.
pub fn assert_versioned_pin(tests_dir: &Path, file: &str, bump: &str, actual: &str) {
    let path = tests_dir.join(file);
    let bump_message = format!(
        "advance {bump}, then record the new versioned file with UPDATE_EXPECT=1; never overwrite a released version's file"
    );
    match fs::read(&path) {
        Ok(expected) => {
            if expected != actual.as_bytes() {
                let expected = String::from_utf8_lossy(&expected);
                let hint = expected
                    .lines()
                    .zip(actual.lines())
                    .enumerate()
                    .find(|(_, (left, right))| left != right)
                    .map_or_else(
                        || {
                            format!(
                                "line count: expected {}, actual {}; first differing byte at {}",
                                expected.lines().count(),
                                actual.lines().count(),
                                expected
                                    .as_bytes()
                                    .iter()
                                    .zip(actual.as_bytes())
                                    .position(|(left, right)| left != right)
                                    .unwrap_or(expected.len().min(actual.len()))
                            )
                        },
                        |(index, (left, right))| {
                            format!("line {}: expected {left:?}, actual {right:?}", index + 1)
                        },
                    );
                panic!("{} differs ({hint}); {bump_message}", path.display());
            }
        }
        Err(error)
            if error.kind() == std::io::ErrorKind::NotFound
                && std::env::var("UPDATE_EXPECT").as_deref() == Ok("1") =>
        {
            fs::write(&path, actual).unwrap();
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            panic!("{} is missing; {bump_message}", path.display());
        }
        Err(error) => panic!("cannot read {}: {error}", path.display()),
    }
}

/// Assert that a result is rejected with the specified error pattern and optional guard.
/// The expression is evaluated once, and the assertion returns `()`.
/// The error type must implement `Debug`; the accepted type need not implement it.
///
/// # Panics
///
/// Panics if the input is accepted or the error does not match the expected pattern.
#[macro_export]
macro_rules! assert_rejects {
    ($expression:expr, $pattern:pat $(if $guard:expr)? $(,)?) => {{
        match $expression {
            Ok(_) => panic!(
                "input was accepted; expected error matching {}",
                stringify!($pattern $(if $guard)?)
            ),
            Err(error) => match error {
                $pattern $(if $guard)? => (),
                actual => panic!(
                    "expected error matching {}; actual error: {:?}",
                    stringify!($pattern $(if $guard)?),
                    actual
                ),
            },
        }
    }};
}

/// Assert that a rejection's display text contains the expected display text.
/// The accepted type need not implement `Debug`.
///
/// # Panics
///
/// Panics if the input is accepted or the error does not contain the expected text.
#[track_caller]
pub fn assert_rejects_with_message<T, E: std::fmt::Display + std::fmt::Debug>(
    result: Result<T, E>,
    expected: impl std::fmt::Display,
) {
    let expected = expected.to_string();
    match result {
        Ok(_) => panic!("input was accepted; expected error containing {expected:?}"),
        Err(error) => assert!(
            error.to_string().contains(&expected),
            "expected error containing {expected:?}; actual error: {error:?}"
        ),
    }
}

/// A temporary directory removed when its guard is dropped.
pub use tempfile::TempDir;

/// Create a guarded temporary directory for a test.
///
/// # Panics
///
/// Panics if the system cannot create a temporary directory.
#[must_use]
pub fn temp_dir() -> TempDir {
    tempfile::Builder::new()
        .prefix("krs-test-")
        .tempdir()
        .expect("test temporary directory is created")
}

/// A generated-fixture target removed when its last guard is dropped.
pub struct SharedFixtureTarget {
    directory: Arc<TempDir>,
}

impl SharedFixtureTarget {
    /// Return the target directory held by this guard.
    #[must_use]
    pub fn path(&self) -> &Path {
        self.directory.path()
    }
}

/// Share a target directory among overlapping generated-fixture tests in this process.
///
/// Tests must hold the guard for their whole duration.
/// Cargo's build-directory lock serializes concurrent nested builds.
/// Each generated fixture must still live in its own fresh directory: its manifest path keys the collector directory and result cache, so fixtures must not share collector or cache state.
/// Tests that do not overlap, including `--test-threads=1`, receive new directories and must rebuild.
///
/// # Panics
///
/// Panics if the target mutex is poisoned or the temporary directory cannot be created.
#[must_use]
pub fn shared_fixture_target() -> SharedFixtureTarget {
    static TARGET: Mutex<Weak<TempDir>> = Mutex::new(Weak::new());
    let mut target = TARGET.lock().expect("fixture target mutex is not poisoned");
    let directory = target.upgrade().unwrap_or_else(|| {
        let directory = Arc::new(temp_dir());
        *target = Arc::downgrade(&directory);
        directory
    });
    SharedFixtureTarget { directory }
}

/// Set the fixture target and disable the environment or Cargo-configured rustc wrapper.
///
/// Nested fixture builds never go through the outer rustc wrapper: generated fixtures live in fresh paths where a caching wrapper only misses, and a shared wrapper server serializes the parallel test processes.
pub fn fixture_build_env(command: &mut Command, target: &Path) {
    command
        .env("CARGO_TARGET_DIR", target)
        .env("RUSTC_WRAPPER", "");
}

/// Select the stable target directory for a checked-in fixture manifest.
///
/// The directory must retain incremental artifacts across runs without writing into fixture sources.
///
/// # Panics
///
/// Panics if a checked-in fixture manifest cannot be resolved.
#[must_use]
pub fn fixture_target(manifest: &Path) -> PathBuf {
    let absolute = manifest
        .canonicalize()
        .expect("checked-in fixture manifest exists");
    let mut hash = 0xcbf2_9ce4_8422_2325_u64;
    for byte in absolute.as_os_str().as_encoded_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100_0000_01b3);
    }
    std::env::temp_dir()
        .join("krs-fixture-targets")
        .join(format!("{hash:016x}"))
}

/// Configure a Cargo invocation against a fixture manifest.
#[must_use]
pub fn cargo_fixture(manifest: impl AsRef<Path>) -> CargoFixture {
    CargoFixture {
        manifest: manifest.as_ref().to_path_buf(),
        args: Vec::new(),
    }
}

/// A fixture Cargo invocation with shared offline and target-directory settings.
pub struct CargoFixture {
    manifest: PathBuf,
    args: Vec<String>,
}

impl CargoFixture {
    /// Add arguments after the Cargo subcommand.
    #[must_use]
    pub fn args(mut self, args: &[&str]) -> Self {
        self.args.extend(args.iter().map(|arg| (*arg).to_owned()));
        self
    }

    /// Run `cargo check` for the fixture.
    #[must_use]
    pub fn check(self) -> Output {
        self.execute("check")
    }

    /// Run `cargo run` for the fixture.
    #[must_use]
    pub fn run(self) -> Output {
        self.execute("run")
    }

    /// Run `cargo test` for the fixture.
    #[must_use]
    pub fn test(self) -> Output {
        self.execute("test")
    }

    /// Run `cargo clippy` for the fixture.
    #[must_use]
    pub fn clippy(self) -> Output {
        self.execute("clippy")
    }

    fn execute(self, subcommand: &str) -> Output {
        let mut command = Command::new(env!("CARGO"));
        fixture_build_env(&mut command, &fixture_target(&self.manifest));
        command
            .arg(subcommand)
            .args(&self.args)
            .arg("--manifest-path")
            .arg(&self.manifest)
            .arg("--offline")
            .env("CARGO_TERM_COLOR", "never")
            .output()
            .expect("fixture Cargo process starts")
    }
}

/// Construct a KRS CLI process using a binary path supplied by the caller.
///
/// KRS CLI integration tests should use [`krs_command!`] so Cargo expands its binary path in the test crate.
#[must_use]
pub fn krs_command(binary: impl AsRef<OsStr>) -> Command {
    Command::new(binary)
}

/// Run the KRS CLI at `binary` with `args` and return its captured output.
///
/// The caller must supply the binary because `CARGO_BIN_EXE_krs` is available only when compiling `krs-cli` integration tests.
///
/// # Panics
///
/// Panics if the CLI process cannot start.
#[must_use]
pub fn krs(binary: impl AsRef<OsStr>, args: &[&str]) -> Output {
    krs_command(binary)
        .args(args)
        .output()
        .expect("KRS CLI process starts")
}

/// Construct a KRS CLI process from Cargo's integration-test binary path or an explicit path.
#[macro_export]
macro_rules! krs_command {
    () => {
        $crate::krs_command(env!("CARGO_BIN_EXE_krs"))
    };
    ($binary:expr) => {
        $crate::krs_command($binary)
    };
}

/// Environment variable naming a directory that receives reference compilations instead of `kompile`.
///
/// When it is set, [`KompileReference::run`] writes `<main>.k` (the source) and `<main>.json` (the
/// main module, syntax module, and search flag) into the directory and does not start `kompile`.
/// The complete IMP gate sets it and compiles each exported source through its recorded reference
/// snapshot, so the gate replays the recorded Java K result by default.
pub const REFERENCE_EXPORT_DIR: &str = "KRS_REFERENCE_EXPORT_DIR";

/// Configure compilation of an emitted K definition with the pinned frontend.
#[must_use]
pub fn kompile_reference<'a>(source: &'a str, main: &str, syntax: &str) -> KompileReference<'a> {
    KompileReference {
        source,
        main: main.to_owned(),
        syntax: syntax.to_owned(),
        enable_search: false,
    }
}

/// A pinned K reference compilation.
pub struct KompileReference<'a> {
    source: &'a str,
    main: String,
    syntax: String,
    enable_search: bool,
}

impl KompileReference<'_> {
    /// Enable search support in the reference definition.
    #[must_use]
    pub fn enable_search(mut self) -> Self {
        self.enable_search = true;
        self
    }

    /// Compile the source and retain its output until the returned guard is dropped.
    ///
    /// When [`REFERENCE_EXPORT_DIR`] is set, export the compilation request there instead and
    /// return an empty directory.
    ///
    /// # Panics
    ///
    /// Panics if the pinned compiler is unavailable, rejects the source, or does not produce
    /// `definition.kore`; or, when exporting, if the request cannot be written or a request for
    /// the same main module already exists.
    #[must_use]
    pub fn run(self) -> TempDir {
        let temporary = temp_dir();
        if let Some(directory) = std::env::var_os(REFERENCE_EXPORT_DIR) {
            self.export(Path::new(&directory));
            return temporary;
        }
        let executable = checked_kompile();
        let source_path = temporary.path().join("definition.k");
        let definition_path = temporary.path().join("compiled");
        std::fs::write(&source_path, self.source).expect("reference source is written");
        let mut process = Command::new(executable);
        process
            .arg(&source_path)
            .arg("--main-module")
            .arg(&self.main)
            .arg("--syntax-module")
            .arg(&self.syntax)
            .arg("--backend")
            .arg("llvm");
        if self.enable_search {
            process.arg("--enable-search");
        }
        let output = process
            .arg("--output-definition")
            .arg(&definition_path)
            .output()
            .expect("pinned kompile process starts");
        assert!(
            output.status.success(),
            "kompile rejected canonical source:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(definition_path.join("definition.kore").is_file());
        temporary
    }

    fn export(&self, directory: &Path) {
        fs::create_dir_all(directory).expect("reference export directory is created");
        let request = serde_json::json!({
            "main": self.main,
            "syntax": self.syntax,
            "enable_search": self.enable_search,
        });
        for (extension, contents) in [
            ("k", self.source.to_owned()),
            ("json", format!("{request}\n")),
        ] {
            let path = directory.join(format!("{}.{extension}", self.main));
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .unwrap_or_else(|error| {
                    panic!("reference export {} is new: {error}", path.display())
                });
            std::io::Write::write_all(&mut file, contents.as_bytes())
                .expect("reference export is written");
        }
    }
}

fn checked_kompile() -> &'static Path {
    static EXECUTABLE: OnceLock<PathBuf> = OnceLock::new();
    EXECUTABLE.get_or_init(|| {
        let lock = include_str!("../../../Krs.lock")
            .parse::<toml_edit::DocumentMut>()
            .expect("Krs.lock is valid TOML");
        let pin = lock
            .get("k")
            .and_then(|item| item.get("version"))
            .and_then(toml_edit::Item::as_str)
            .expect("Krs.lock has a K version");
        let executable = std::env::var_os("KRS_K_BIN").map_or_else(
            || PathBuf::from("kompile"),
            |dir| PathBuf::from(dir).join("kompile"),
        );
        let output = Command::new(&executable)
            .arg("--version")
            .output()
            .expect("pin-matched kompile must be on PATH or in KRS_K_BIN");
        assert!(output.status.success());
        let version_output = String::from_utf8_lossy(&output.stdout);
        let version_token = version_output.split_whitespace().find(|token| {
            token.starts_with('v') && token.chars().nth(1).is_some_and(|ch| ch.is_ascii_digit())
        });
        assert_eq!(
            version_token,
            Some(format!("v{pin}").as_str()),
            "kompile must match K v{pin}"
        );
        executable
    })
}
