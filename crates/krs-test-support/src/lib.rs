//! Shared assertions and fixture support for KRS tests.
//!
//! Fixture builds must set `CARGO_TARGET_DIR` through [`fixture_target`].
//! Generated fixtures use a target inside their guarded scratch directory.
//! Checked-in fixtures use a stable directory in the system temporary root, keyed by the absolute manifest path; this preserves incremental builds across test runs without writing into fixture sources.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

mod compile_fixtures;
pub use compile_fixtures::{Expectation, check_compile_fixtures};

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

/// Select the target directory for a fixture manifest.
///
/// `scratch` must be the guarded root for a generated fixture.
/// Pass `None` for a checked-in fixture to retain incremental artifacts across runs.
///
/// # Panics
///
/// Panics if a checked-in fixture manifest cannot be resolved.
#[must_use]
pub fn fixture_target(manifest: &Path, scratch: Option<&Path>) -> PathBuf {
    if let Some(scratch) = scratch {
        return scratch.join("target");
    }
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
        Command::new(env!("CARGO"))
            .arg(subcommand)
            .args(&self.args)
            .arg("--manifest-path")
            .arg(&self.manifest)
            .arg("--offline")
            .env("CARGO_TERM_COLOR", "never")
            .env("CARGO_TARGET_DIR", fixture_target(&self.manifest, None))
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
    /// # Panics
    ///
    /// Panics if the pinned compiler is unavailable, rejects the source, or does not produce `definition.kore`.
    #[must_use]
    pub fn run(self) -> TempDir {
        let executable = checked_kompile();
        let temporary = temp_dir();
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
