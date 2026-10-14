// fs::canonicalize, fs::read, fs::metadata, and fs::read_dir over the case
// VFS (preopen "/" holding /data), as the collector reads manifests and
// sources (collector runner, canonicalize probe). Errors print io::ErrorKind, the raw
// WASI errno, and the message.
use std::fmt::Debug;
use std::fs;
use std::io;

fn show<T: Debug>(label: &str, result: io::Result<T>) {
    match result {
        Ok(value) => println!("{label}: Ok({value:?})"),
        Err(error) => println!(
            "{label}: Err(kind={:?}, os={:?}, message={:?})",
            error.kind(),
            error.raw_os_error(),
            error.to_string()
        ),
    }
}

fn main() {
    let paths = [
        ("existing-file", "/data/dir/file.txt"),
        ("existing-directory", "/data/dir"),
        ("directory-trailing-slash", "/data/dir/"),
        ("missing-file", "/data/dir/missing.txt"),
        ("dot-dot", "/data/dir/sub/../file.txt"),
        ("dot-component", "/data/./dir/file.txt"),
        ("missing-parent", "/data/missing-parent/file.txt"),
        ("root", "/"),
    ];
    for (label, path) in paths {
        show(&format!("canonicalize {label}"), fs::canonicalize(path));
    }
    for (label, path) in paths {
        show(
            &format!("read {label}"),
            fs::read(path).map(|bytes| (bytes.len(), String::from_utf8_lossy(&bytes).into_owned())),
        );
    }
    for (label, path) in paths {
        show(
            &format!("metadata {label}"),
            fs::metadata(path).map(|meta| (meta.is_file(), meta.is_dir(), if meta.is_file() { meta.len() } else { 0 })),
        );
    }
    show(
        "read_dir /data/dir",
        fs::read_dir("/data/dir").and_then(|entries| {
            let mut names = entries
                .map(|entry| entry.map(|entry| entry.file_name().to_string_lossy().into_owned()))
                .collect::<io::Result<Vec<_>>>()?;
            names.sort();
            Ok(names)
        }),
    );
    show("read_to_string missing", fs::read_to_string("/data/dir/missing.txt"));
    // The structured error the collector reports for a missing source (Failure::io).
    if let Err(error) = fs::canonicalize("/data/dir/missing.txt") {
        println!(
            "{{\"error\":{{\"kind\":\"{:?}\",\"message\":\"{}\",\"path\":\"/data/dir/missing.txt\"}}}}",
            error.kind(),
            error
        );
    }
}
