use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

static TEMP_ID: AtomicU64 = AtomicU64::new(0);

struct TemporaryRepository {
    root: PathBuf,
}

impl TemporaryRepository {
    fn with_vector(bytes: Option<&[u8]>) -> Self {
        let root = std::env::temp_dir().join(format!(
            "kink-conformance-{}-{}",
            std::process::id(),
            TEMP_ID.fetch_add(1, Ordering::Relaxed)
        ));
        let vector_directory = root.join("investigations/backend-agnostic-goal-closure/vectors");
        fs::create_dir_all(&vector_directory).expect("temporary vector directory is writable");
        if let Some(bytes) = bytes {
            fs::write(
                vector_directory.join("canonicalization-vectors.json"),
                bytes,
            )
            .expect("temporary vector is writable");
        }
        Self { root }
    }
}

impl Drop for TemporaryRepository {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.root).expect("temporary repository is removable");
    }
}

fn workspace_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("conformance crate is below the workspace root")
}

fn invoke(current_dir: &Path, arguments: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_kink-conformance"))
        .args(arguments)
        .current_dir(current_dir)
        .output()
        .expect("conformance CLI starts")
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn default_discovery_is_independent_of_process_working_directory() {
    let root_output = invoke(workspace_root(), &["check"]);
    let nested_output = invoke(
        &workspace_root().join("crates/kink-portable/src"),
        &["check"],
    );
    assert!(root_output.status.success(), "{}", stderr(&root_output));
    assert!(nested_output.status.success(), "{}", stderr(&nested_output));
    assert_eq!(root_output.stdout, nested_output.stdout);
    assert_eq!(
        String::from_utf8_lossy(&root_output.stdout),
        "PASS canonicalization-vectors: 9 cases; identity-vectors: 7 cases; portable-definitions: 4 fixtures\n"
    );
}

#[test]
fn list_reports_the_frozen_input_family() {
    let output = invoke(workspace_root(), &["list"]);
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stdout),
        "canonicalization-vectors\tvectors/canonicalization-vectors.json\t9\nidentity-vectors\tvectors/identity-vectors.json\t7\n"
    );
}

#[test]
fn missing_vector_is_a_typed_nonzero_failure() {
    let repository = TemporaryRepository::with_vector(None);
    let output = invoke(
        workspace_root(),
        &[
            "--repository",
            repository.root.to_str().expect("temporary path is UTF-8"),
            "check",
        ],
    );
    assert_eq!(output.status.code(), Some(3));
    assert!(stderr(&output).starts_with("E_INPUT_NOT_FOUND"));
}

#[test]
fn malformed_vector_is_a_typed_nonzero_failure() {
    let repository = TemporaryRepository::with_vector(Some(b"{not-json"));
    let output = invoke(
        workspace_root(),
        &[
            "--repository",
            repository.root.to_str().expect("temporary path is UTF-8"),
            "check",
        ],
    );
    assert_eq!(output.status.code(), Some(5));
    assert!(stderr(&output).starts_with("E_MALFORMED_INPUT"));
}

#[test]
fn unexpected_envelope_field_is_a_typed_nonzero_failure() {
    let repository = TemporaryRepository::with_vector(Some(
        br#"{"schemaVersion":1,"packageVersion":"backend-agnostic-k-in-k-v1","cases":[{"id":"case"}],"unexpected":true}"#,
    ));
    let output = invoke(
        workspace_root(),
        &[
            "--repository",
            repository.root.to_str().expect("temporary path is UTF-8"),
            "check",
        ],
    );
    assert_eq!(output.status.code(), Some(5));
    assert!(stderr(&output).starts_with("E_MALFORMED_INPUT"));
}

#[test]
fn unexpected_cli_argument_is_a_typed_nonzero_failure() {
    let output = invoke(workspace_root(), &["check", "extra"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(stderr(&output).starts_with("E_UNEXPECTED_INPUT"));
}
