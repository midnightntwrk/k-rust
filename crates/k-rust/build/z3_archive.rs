//! The Z3 archive a static link of this build takes its Z3 code from, for `k_rust::backend::z3_build`.
//!
//! How many resource units Z3 counts for a query is a function of the code that searches, so the
//! build a resource-bounded answer depends on is named by the file that code comes from. When Z3
//! is linked dynamically that file is the shared library, which the running process reads
//! itself. When it is linked statically the code is inside the executable, among everything else
//! the executable holds, so no digest the process can take of itself names Z3 alone: the digest of
//! the executable changes with every change to the program around Z3. The archive (`libz3.a`) the
//! link takes Z3 from does name it, and only the build knows which archive that is, so this
//! script records its SHA-256 as `K_RUST_Z3_ARCHIVE_SHA256`, and the Z3 release the archive
//! holds as `K_RUST_Z3_ARCHIVE_RELEASE` (both empty when it cannot say).
//!
//! The archive follows from the route that provides Z3 to `z3-sys`:
//! - k-rust's `z3-inference-gh-release` feature (`z3-sys`'s `gh-release`): `z3-sys` downloads the
//!   published release asset for the target and links its `libz3.a` statically. The asset is
//!   fixed by the release, the target's architecture and its OS, so its archive is named by the
//!   digest [`PUBLISHED`] lists for it. `z3-sys` downloads into its own build directory, which no
//!   other build script can read, and does not check what it downloads, so the digest is the
//!   published asset's, not a measurement of the download; a release or target [`PUBLISHED`] does
//!   not list records nothing.
//! - otherwise, the environment route: the linker resolves `-lz3` in the first directory of its
//!   search path that holds a `libz3`, taking the shared library there unless the link is static
//!   (`Z3_STATIC` or `PKG_CONFIG_ALL_STATIC`) or the directory holds only the archive. Of that
//!   path this script sees `Z3_LIBRARY_PATH_OVERRIDE` (which `z3-sys` passes first) and
//!   `LIBRARY_PATH` (which the linker searches after the paths it is given); when the first of
//!   their directories that holds a `libz3` gives the archive, the digest is that file's. A
//!   shared library there, or no such directory, records nothing: the link is dynamic, or takes an
//!   archive from a path this script does not see, such as a `pkg-config` file's.
//!
//! `z3_build` uses the record only when the running process finds Z3's code inside its own image,
//! so a link that turned out dynamic is named by its shared library instead, and only when the
//! release the record names is the release the linked Z3 reports.

use std::path::{Path, PathBuf};

/// The `libz3.a` of each published release asset `z3-sys`'s `gh-release` downloads: the release,
/// the target's architecture and OS as Cargo names them, the asset, and the archive's SHA-256.
const PUBLISHED: &[(&str, &str, &str, &str, &str)] = &[(
    "4.16.0",
    "x86_64",
    "linux",
    // The asset `.github/actions/krs-z3` downloads and checks by the digest of its zip.
    "z3-4.16.0-x64-glibc-2.39",
    "be85aeff225c953bee73df3b3eec46adcadf68d03b0b47a50cbb2e4bf1fe52cb",
)];

/// The release `z3-sys`'s `gh-release` downloads when `Z3_SYS_Z3_VERSION` is unset.
const GH_RELEASE_DEFAULT: &str = "4.16.0";

/// The archive this build links Z3 from: its SHA-256, as lowercase hexadecimal, and the Z3
/// release it holds (`4.16.0`); `None` when the build links no Z3, links it dynamically, or takes
/// an archive it cannot name. Prints the rerun triggers of what it reads.
pub fn z3_archive() -> Option<(String, String)> {
    for variable in [
        "Z3_SYS_Z3_VERSION",
        "Z3_LIBRARY_PATH_OVERRIDE",
        "LIBRARY_PATH",
        "Z3_STATIC",
        "PKG_CONFIG_ALL_STATIC",
    ] {
        println!("cargo::rerun-if-env-changed={variable}");
    }
    std::env::var_os("CARGO_FEATURE_Z3_INFERENCE")?;
    if std::env::var_os("CARGO_FEATURE_Z3_INFERENCE_GH_RELEASE").is_some() {
        let release =
            std::env::var("Z3_SYS_Z3_VERSION").unwrap_or_else(|_| GH_RELEASE_DEFAULT.to_owned());
        let arch = std::env::var("CARGO_CFG_TARGET_ARCH").ok()?;
        let os = std::env::var("CARGO_CFG_TARGET_OS").ok()?;
        return PUBLISHED
            .iter()
            .find(|(r, a, o, _, _)| *r == release && *a == arch && *o == os)
            .map(|(release, _, _, _, digest)| ((*digest).to_owned(), (*release).to_owned()));
    }
    let static_link = ["Z3_STATIC", "PKG_CONFIG_ALL_STATIC"]
        .iter()
        .any(|variable| std::env::var_os(variable).is_some_and(|value| !value.is_empty()));
    let mut directories: Vec<PathBuf> = std::env::var_os("Z3_LIBRARY_PATH_OVERRIDE")
        .map(PathBuf::from)
        .into_iter()
        .collect();
    if let Some(paths) = std::env::var_os("LIBRARY_PATH") {
        directories
            .extend(std::env::split_paths(&paths).filter(|path| !path.as_os_str().is_empty()));
    }
    for directory in directories {
        let archive = directory.join("libz3.a");
        let shared = directory.join("libz3.so");
        let (has_archive, has_shared) = (archive.is_file(), shared.exists());
        // A missing trigger would rerun this script on every build, so only files that exist.
        for file in [(has_archive, &archive), (has_shared, &shared)]
            .into_iter()
            .filter_map(|(exists, file)| exists.then_some(file))
        {
            println!("cargo::rerun-if-changed={}", file.display());
        }
        if !has_archive && !has_shared {
            continue;
        }
        if has_archive && (static_link || !has_shared) {
            return archive_identity(&archive);
        }
        return None;
    }
    None
}

/// The SHA-256 of the archive at `path`, as lowercase hexadecimal, and the one Z3 release whose
/// full-version literal (`Z3 4.16.0.0`, the string `Z3_get_full_version` returns) it holds;
/// `None` when it cannot be read or holds no such literal or several.
fn archive_identity(path: &Path) -> Option<(String, String)> {
    use sha2::{Digest, Sha256};
    let bytes = std::fs::read(path).ok()?;
    let digest = Sha256::digest(&bytes)
        .iter()
        .fold(String::with_capacity(64), |mut hex, byte| {
            use std::fmt::Write;
            let _ = write!(hex, "{byte:02x}");
            hex
        });
    let mut releases = std::collections::BTreeSet::new();
    for (start, _) in bytes.windows(3).enumerate().filter(|(_, w)| *w == b"Z3 ") {
        let literal = &bytes[start + 3..];
        let Some(end) = literal.iter().position(|byte| *byte == 0) else {
            continue;
        };
        let Ok(version) = std::str::from_utf8(&literal[..end]) else {
            continue;
        };
        let parts: Vec<&str> = version.split('.').collect();
        if parts.len() == 4
            && parts
                .iter()
                .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()))
        {
            releases.insert(parts[..3].join("."));
        }
    }
    let mut releases = releases.into_iter();
    match (releases.next(), releases.next()) {
        (Some(release), None) => Some((digest, release)),
        _ => None,
    }
}
