//! End-to-end formatting against temporary Cargo packages.

use std::fs;

use krs_fmt::{Edition, FormatOptions, format_file};
use krs_test_support::{krs_command, temp_dir};

#[test]
fn formats_a_2021_package_from_another_directory() {
    let temporary = temp_dir();
    let root = temporary.path();
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"format-edition\"\nversion = \"0.1.0\"\nedition = \"2021\"\n[workspace]\n",
    )
    .unwrap();
    let source = root.join("src/lib.rs");
    fs::write(&source, "use std::{u8, u16};\n").unwrap();
    let manifest = root.join("Cargo.toml");
    let result = krs_command!()
        .current_dir(std::env::temp_dir())
        .arg("fmt")
        .args(["--manifest-path", manifest.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(
        fs::read_to_string(&source).unwrap(),
        "use std::{u16, u8};\n"
    );

    let check = krs_command!()
        .arg("fmt")
        .args([
            "--check",
            "--manifest-path",
            manifest.to_str().unwrap(),
            source.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        check.status.success(),
        "{}",
        String::from_utf8_lossy(&check.stderr)
    );
}

#[test]
fn file_formatting_uses_rustfmt_config_in_the_file_directory() {
    let temporary = temp_dir();
    let root = temporary.path();
    fs::create_dir_all(root.join("source")).unwrap();
    fs::write(root.join("source/rustfmt.toml"), "hard_tabs = true\n").unwrap();
    let source = root.join("source/lib.rs");
    fs::write(&source, "fn example() { let value = 1; }\n").unwrap();
    let formatted = format_file(
        &source,
        FormatOptions {
            edition: Edition::E2021,
            ..FormatOptions::default()
        },
    )
    .unwrap();
    assert!(formatted.output.contains("\tlet value = 1;"));
}

#[test]
fn workspace_check_skips_the_configured_target_directory_but_not_build_modules() {
    let temporary = temp_dir();
    let root = temporary.path();
    for directory in ["src/build", ".cargo", "out", "tests/fixtures/nested/src"] {
        fs::create_dir_all(root.join(directory)).unwrap();
    }
    fs::write(
        root.join("Cargo.toml"),
        "[package]\nname = \"format-target-dir\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n",
    )
    .unwrap();
    fs::write(
        root.join(".cargo/config.toml"),
        "[build]\ntarget-dir = \"out\"\n",
    )
    .unwrap();
    fs::write(
        root.join("tests/fixtures/nested/Cargo.toml"),
        "[package]\nname = \"nested\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[workspace]\n",
    )
    .unwrap();
    fs::write(root.join("src/lib.rs"), "mod build;\n").unwrap();
    // The build script's target walks the package root,
    // which holds the configured target directory and the nested package.
    fs::write(root.join("build.rs"), "fn main() {}\n").unwrap();
    let unformatted = "pub fn f( ) {}\n";
    for file in [
        "src/build/mod.rs",
        "out/generated.rs",
        "tests/fixtures/nested/src/lib.rs",
    ] {
        fs::write(root.join(file), unformatted).unwrap();
    }
    // The configured target directory is observed only without an environment override.
    let check = krs_command!()
        .current_dir(root)
        .env_remove("CARGO_TARGET_DIR")
        .env_remove("CARGO_BUILD_TARGET_DIR")
        .args(["fmt", "--check"])
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&check.stderr);
    assert!(!check.status.success(), "{stderr}");
    assert!(stderr.contains("src/build/mod.rs"), "{stderr}");
    assert!(!stderr.contains("generated.rs"), "{stderr}");
    assert!(!stderr.contains("nested"), "{stderr}");
}
