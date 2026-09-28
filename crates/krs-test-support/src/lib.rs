//! Shared support for integration tests that invoke Cargo, the KRS CLI, or K.
//!
//! Fixture builds must set `CARGO_TARGET_DIR` through [`fixture_target`].
//! Generated fixtures use a target inside their guarded scratch directory.
//! Checked-in fixtures use a stable directory in the system temporary root, keyed by the absolute manifest path; this preserves incremental builds across test runs without writing into fixture sources.

use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::OnceLock;

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
        let pin = include_str!("../../../Krs.lock")
            .split("[k]\n")
            .nth(1)
            .expect("Krs.lock contains a K pin")
            .lines()
            .find_map(|line| {
                line.strip_prefix("version = \"")
                    .and_then(|part| part.strip_suffix('"'))
            })
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
        assert!(
            String::from_utf8_lossy(&output.stdout).contains(&format!("v{pin}")),
            "kompile must match K v{pin}"
        );
        executable
    })
}
