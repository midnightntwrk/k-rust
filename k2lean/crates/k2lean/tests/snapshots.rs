//! Snapshot tests: `k2lean gen` on the small K fixtures of `../../tests/fixtures/` (krust-compiled
//! KORE, checked in) must write exactly the Lean project recorded in each fixture's `expected/`.
//! A difference is a change of the generated Lean; if it is intended, bless the new output with
//! `gate/fixtures/regen.sh --bless` (or `K2LEAN_BLESS=1 cargo test --test snapshots`) and review
//! the diff of `expected/`.

use std::path::{Path, PathBuf};
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn files(root: &Path) -> Vec<PathBuf> {
    fn walk(root: &Path, dir: &Path, out: &mut Vec<PathBuf>) {
        for e in std::fs::read_dir(dir).unwrap() {
            let p = e.unwrap().path();
            if p.is_dir() {
                walk(root, &p, out);
            } else {
                out.push(p.strip_prefix(root).unwrap().to_path_buf());
            }
        }
    }
    let mut out = Vec::new();
    if root.exists() {
        walk(root, root, &mut out);
    }
    out.sort();
    out
}

/// Generate the fixture's project into a fresh directory and return it.
pub fn generate(name: &str, ns: &str, extra: &[&str]) -> PathBuf {
    let fx = fixture(name);
    let tag: String = extra
        .iter()
        .map(|x| x.trim_start_matches('-'))
        .filter(|x| !x.contains('/'))
        .collect::<Vec<_>>()
        .join("-");
    let out = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("snap-{name}-{tag}"));
    let _ = std::fs::remove_dir_all(&out);
    let o = Command::new(env!("CARGO_BIN_EXE_k2lean"))
        .arg("gen")
        .arg("--kore")
        .arg(fx.join("definition.kore"))
        .arg("--runtime")
        .arg(fx.join("runtime.json"))
        .arg("--out")
        .arg(&out)
        .args(["--name", ns, "--prelude", "../../prelude"])
        .args(extra)
        .output()
        .unwrap();
    assert!(
        o.status.success(),
        "k2lean gen {name} failed:\n{}",
        String::from_utf8_lossy(&o.stderr)
    );
    out
}

/// The snapshot of `gen`, recorded in the fixture's `expected/`.
fn snapshot(name: &str, ns: &str) {
    snapshot_with(name, ns, &[], "expected");
}

/// The snapshot of `gen` with `extra` flags, recorded in the fixture's directory `dir`.
fn snapshot_with(name: &str, ns: &str, extra: &[&str], dir: &str) {
    let out = generate(name, ns, extra);
    let exp = fixture(name).join(dir);
    if std::env::var("K2LEAN_BLESS").is_ok_and(|v| v == "1") {
        let _ = std::fs::remove_dir_all(&exp);
        for f in files(&out) {
            std::fs::create_dir_all(exp.join(&f).parent().unwrap()).unwrap();
            std::fs::copy(out.join(&f), exp.join(&f)).unwrap();
        }
        eprintln!("blessed {}", exp.display());
        return;
    }
    let (got, want) = (files(&out), files(&exp));
    let mut problems = Vec::new();
    for f in want.iter().filter(|f| !got.contains(f)) {
        problems.push(format!("{}: no longer generated", f.display()));
    }
    for f in got.iter().filter(|f| !want.contains(f)) {
        problems.push(format!("{}: newly generated", f.display()));
    }
    for f in got.iter().filter(|f| want.contains(f)) {
        let a = std::fs::read_to_string(exp.join(f)).unwrap();
        let b = std::fs::read_to_string(out.join(f)).unwrap();
        if a != b {
            let (al, bl): (Vec<&str>, Vec<&str>) = (a.lines().collect(), b.lines().collect());
            let i = al
                .iter()
                .zip(&bl)
                .position(|(x, y)| x != y)
                .unwrap_or(al.len().min(bl.len()));
            problems.push(format!(
                "{}: differs from line {}:\n    expected: {}\n    got:      {}",
                f.display(),
                i + 1,
                al.get(i).unwrap_or(&"<end of file>"),
                bl.get(i).unwrap_or(&"<end of file>")
            ));
        }
    }
    assert!(
        problems.is_empty(),
        "generated Lean for fixture {name} differs from {} ({} files):\n{}\nif intended: gate/fixtures/regen.sh --bless",
        exp.display(),
        problems.len(),
        problems.join("\n")
    );
}

/// Recursion (a self-recursive and a mutually recursive pair), a non-recursive partial function,
/// an `owise` equation, one labelled and one unlabelled rule.
#[test]
fn peano() {
    snapshot("peano", "Peano");
}

/// Int, Map and Id from domains.md, a cell with a map, a partial function with an `owise`
/// equation, a labelled rule, and two priority ranks (the stratified `Step`): the `Term` family,
/// fallback arms on every non-variable match, the collections' `ListSizeOf` instances, and
/// determinism along the rule index.
#[test]
fn counter() {
    snapshot("counter", "Counter");
}

/// Function equations with a free-key map pattern `K |-> V REST` (`MapHook.chooseFirst`): not
/// recursive (`hasNeg`, with an `owise` equation), recursive over a map (`allNat`) and over a
/// cell map (`total`), whose termination comes from the collections' `ListSizeOf`.
#[test]
fn freekey() {
    snapshot("freekey", "FreeKey");
}

/// A hook the hook library does not implement (`Bytes2Hex`) and a function without equations
/// (`oracle`): the fields of the generated `Hooks` class, with `variable [Hooks]` in the modules
/// after `Terms`; `Int2Bytes` and `Bytes2Int` through their generated adapters.
#[test]
fn params() {
    snapshot("params", "Params");
}

/// Termination measures: a negated earlier guard (`sumTo`), a constructor rank (`fee`), and a
/// least fixed point (`norm`, from the fixture's `--termination` file).
#[test]
fn measure() {
    let side = fixture("measure").join("termination.toml");
    snapshot_with(
        "measure",
        "Measure",
        &["--termination", side.to_str().unwrap()],
        "expected",
    );
}
