//! `[[program]]` entries that name a pattern of case files (`files`, `cases`): each match is a
//! program whose id is its path relative to the manifest's directory; adding or removing a
//! matching file adds or removes a program; the program order is the ids' order; a pattern that
//! matches nothing, an invalid pattern and an id given twice are manifest errors; a case
//! document's inputs name files relative to the document; every document reports the ids.

use kink_corpus::ProgramSource;
use kink_flow::{
    FlowManifest,
    admit::{FlowAdmission, admit},
    cli::{check, results, run},
    manifest::{ManifestError, Program},
    results::ResultsOptions,
    search::RunOptions,
};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-cases-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write(path: &Path, text: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, text).unwrap();
}

const SPEC: &str = "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\n";

fn read(dir: &Path) -> Result<FlowManifest, ManifestError> {
    FlowManifest::read(&dir.join("FLOW.toml"))
}

fn ids(manifest: &FlowManifest) -> Vec<&str> {
    manifest.programs.iter().map(|p| p.id.as_str()).collect()
}

/// A scratch directory holding `files` (empty unless given) and the manifest `SPEC + programs`.
fn corpus(name: &str, files: &[&str], programs: &str) -> PathBuf {
    let dir = scratch(name);
    for file in files {
        write(&dir.join(file), "1 + 2");
    }
    write(&dir.join("FLOW.toml"), &format!("{SPEC}{programs}"));
    dir
}

#[track_caller]
fn assert_error(dir: &Path, key: &str, message: &str) {
    let error = read(dir).expect_err("the manifest must be refused");
    assert_eq!(error.key, key, "{error}");
    assert!(error.message.contains(message), "{error}");
}

/// A `files` entry is replaced in place by its matches, sorted by id, each a program text
/// `file = <match>` with the entry's other keys; the id is the matched path. Wildcards skip names
/// that start with `.` (the cache directory among them), `**` matches zero or more directories,
/// and a directory is no match.
#[test]
fn a_files_entry_is_its_matches_in_place_sorted_by_path() {
    let dir = corpus(
        "files",
        &[
            "programs/sub.calc",
            "programs/add.calc",
            "programs/deep/er/mul.calc",
            "programs/.hidden.calc",
            "programs/.kink-flow/cached.calc",
            "programs/notes.txt",
        ],
        r#"
[[program]]
id = "first"
text = "1"

[[program]]
files = "programs/**/*.calc"
start_sort = "Exp"
variables = { N = "1" }

[[program]]
id = "last"
text = "2"
"#,
    );
    fs::create_dir_all(dir.join("programs/dir.calc")).unwrap();
    let manifest = read(&dir).unwrap();
    assert_eq!(
        ids(&manifest),
        [
            "first",
            "programs/add.calc",
            "programs/deep/er/mul.calc",
            "programs/sub.calc",
            "last"
        ]
    );
    assert_eq!(
        manifest.programs[1],
        Program {
            id: "programs/add.calc".into(),
            source: Some(ProgramSource::File("programs/add.calc".into())),
            start_sort: Some("Exp".into()),
            variables: vec![("N".into(), "1".into())],
            inputs: toml::Table::new(),
            case: None,
            case_file: None,
            expect: None,
            stop_count: None,
        }
    );
    // A literal component may name a hidden directory; `*` and `?` match within one name.
    let hidden = corpus(
        "hidden-literal",
        &[".cases/t1.calc", ".cases/t22.calc", ".cases/u1.calc"],
        "[[program]]\nfiles = \".cases/t?.calc\"\n",
    );
    assert_eq!(ids(&read(&hidden).unwrap()), [".cases/t1.calc"]);
    // A glob whose own first character is `.` matches dot names; one starting with a wildcard
    // does not.
    let dot_glob = corpus(
        "hidden-glob",
        &[".cases1/a.calc", ".cases2/b.calc", "cases3/c.calc"],
        "[[program]]\nfiles = \".cases*/*.calc\"\n\n[[program]]\nfiles = \"?ases*/*.calc\"\n",
    );
    assert_eq!(
        ids(&read(&dot_glob).unwrap()),
        [".cases1/a.calc", ".cases2/b.calc", "cases3/c.calc"]
    );
    // A trailing `**` matches every file below.
    let below = corpus(
        "trailing-double-star",
        &["all/a.calc", "all/x/b.txt", "all/.c"],
        "[[program]]\nfiles = \"all/**\"\n",
    );
    assert_eq!(ids(&read(&below).unwrap()), ["all/a.calc", "all/x/b.txt"]);
}

/// Adding a matching file adds a program and removing one removes it, without editing the
/// manifest; the other programs keep their ids. The same corpus in another directory has the same
/// programs: no id depends on where the corpus is.
#[test]
fn adding_or_removing_a_matching_file_adds_or_removes_its_program() {
    let entry = "[[program]]\nfiles = \"cases/*.calc\"\n";
    let dir = corpus("add-remove", &["cases/b.calc", "cases/d.calc"], entry);
    assert_eq!(ids(&read(&dir).unwrap()), ["cases/b.calc", "cases/d.calc"]);
    write(&dir.join("cases/c.calc"), "3");
    assert_eq!(
        ids(&read(&dir).unwrap()),
        ["cases/b.calc", "cases/c.calc", "cases/d.calc"]
    );
    fs::remove_file(dir.join("cases/b.calc")).unwrap();
    assert_eq!(ids(&read(&dir).unwrap()), ["cases/c.calc", "cases/d.calc"]);

    let elsewhere = corpus(
        "add-remove-elsewhere/nested",
        &["cases/d.calc", "cases/c.calc"],
        entry,
    );
    let (here, there) = (read(&dir).unwrap(), read(&elsewhere).unwrap());
    assert_eq!(here.programs, there.programs);
}

/// `**` never descends through a link (a link cycle cannot make the walk infinite); a literal or
/// glob component follows one; a dangling link is a match, refused when its file is read.
#[cfg(unix)]
#[test]
fn double_star_does_not_follow_links() {
    let dir = corpus(
        "links",
        &["real/a.calc"],
        "[[program]]\nfiles = \"**/*.calc\"\n\n[[program]]\nfiles = \"linked/*.calc\"\n",
    );
    std::os::unix::fs::symlink(dir.join("real"), dir.join("linked")).unwrap();
    std::os::unix::fs::symlink(&dir, dir.join("real/cycle")).unwrap();
    std::os::unix::fs::symlink(dir.join("missing.calc"), dir.join("real/dangling.calc")).unwrap();
    assert_eq!(
        ids(&read(&dir).unwrap()),
        [
            "real/a.calc",
            "real/dangling.calc",
            "linked/a.calc",
            "linked/dangling.calc"
        ]
    );
}

/// A name that is not UTF-8 is ignored unless the pattern matches a path through it, which no id
/// could name: then it is an error naming the match.
#[cfg(unix)]
#[test]
fn a_name_that_is_not_utf8_is_an_error_only_when_matched() {
    use std::os::unix::ffi::OsStrExt;
    let not_utf8 = |name: &[u8]| std::ffi::OsStr::from_bytes(name).to_owned();
    let dir = corpus(
        "not-utf8",
        &["programs/sum.imp", "programs/deep/mul.imp"],
        "[[program]]\nfiles = \"programs/*.imp\"\n",
    );
    let programs = dir.join("programs");
    fs::write(programs.join(not_utf8(b"\xff.bak")), "").unwrap();
    fs::write(programs.join(not_utf8(b".\xff.imp")), "").unwrap();
    fs::create_dir(programs.join(not_utf8(b"\xfe"))).unwrap();
    fs::write(programs.join(not_utf8(b"\xfe")).join("notes.txt"), "").unwrap();
    assert_eq!(ids(&read(&dir).unwrap()), ["programs/sum.imp"]);
    write(
        &dir.join("FLOW.toml"),
        &format!("{SPEC}[[program]]\nfiles = \"programs/**/*.imp\"\n"),
    );
    assert_eq!(
        ids(&read(&dir).unwrap()),
        ["programs/deep/mul.imp", "programs/sum.imp"]
    );
    fs::write(programs.join(not_utf8(b"\xfe")).join("lost.imp"), "").unwrap();
    assert_error(&dir, "program[0].files", "\u{fffd}/lost.imp (read lossily)");
    fs::remove_file(programs.join(not_utf8(b"\xfe")).join("lost.imp")).unwrap();
    fs::write(programs.join(not_utf8(b"\xff.imp")), "").unwrap();
    assert_error(&dir, "program[0].files", "not UTF-8");
}

/// A named pipe the pattern matches is an error at decoding (reading it could block for good);
/// one the pattern does not match is ignored.
#[cfg(unix)]
#[test]
fn a_special_file_that_matches_is_an_error() {
    let dir = corpus(
        "special",
        &["tests/a.toml"],
        "[[program]]\ncases = \"tests/**/*.toml\"\n",
    );
    write(&dir.join("tests/a.toml"), "[inputs]\nn = 1\n");
    let fifo = |path: &Path| {
        let status = std::process::Command::new("mkfifo")
            .arg(path)
            .status()
            .unwrap();
        assert!(status.success());
    };
    fifo(&dir.join("tests/ctl.pipe"));
    assert_eq!(ids(&read(&dir).unwrap()), ["tests/a.toml"]);
    fifo(&dir.join("tests/ctl.toml"));
    assert_error(
        &dir,
        "program[0].cases",
        "tests/ctl.toml matches and is not a regular file",
    );
}

/// A pattern that matches nothing is an error, not an empty corpus; so is every pattern the
/// syntax refuses, and every key that does not belong beside a pattern.
#[test]
fn pattern_errors_name_the_entry() {
    let cases: &[(&str, &str, &str)] = &[
        (
            "files = \"cases/*.calc\"",
            "program[0].files",
            "matches no file",
        ),
        (
            "cases = \"cases/*.toml\"",
            "program[0].cases",
            "matches no file",
        ),
        ("files = \"\"", "program[0].files", "must not be empty"),
        ("files = 3", "program[0].files", "expected a string"),
        (
            "files = \"/cases/*.calc\"",
            "program[0].files",
            "is absolute",
        ),
        (
            "files = \"cases//*.calc\"",
            "program[0].files",
            "empty component",
        ),
        ("files = \"cases/\"", "program[0].files", "empty component"),
        (
            "files = \"../*.calc\"",
            "program[0].files",
            "a `..` component",
        ),
        (
            "files = \"./*.calc\"",
            "program[0].files",
            "a `.` component",
        ),
        ("files = \"cases/[ab].calc\"", "program[0].files", "has `[`"),
        (
            "files = \"cases/{a,b}.calc\"",
            "program[0].files",
            "has `{`",
        ),
        ("files = 'cases\\*.calc'", "program[0].files", "has `\\`"),
        (
            "files = \"cases/a**.calc\"",
            "program[0].files",
            "whole component",
        ),
        (
            "files = \"cases/one.calc\"",
            "program[0].files",
            "has no wildcard",
        ),
        (
            "cases = \"cases/*.json\"",
            "program[0].cases",
            "must end in `.toml`",
        ),
        (
            "cases = \"cases/*\"",
            "program[0].cases",
            "must end in `.toml`",
        ),
        (
            "files = \"cases/*.calc\"\ncases = \"cases/*.toml\"",
            "program[0]",
            "has both files and cases",
        ),
        (
            "files = \"cases/*.calc\"\nid = \"x\"",
            "program[0].id",
            "remove id",
        ),
        (
            "cases = \"cases/*.toml\"\nid = \"x\"",
            "program[0].id",
            "remove id",
        ),
        (
            "files = \"cases/*.calc\"\nfile = \"a.calc\"",
            "program[0].file",
            "the matches of `files` are the program texts",
        ),
        (
            "files = \"cases/*.calc\"\ntext = \"1\"",
            "program[0].text",
            "the matches of `files` are the program texts",
        ),
        (
            "files = \"cases/*.calc\"\nfrom = \"x\"",
            "program[0].from",
            "unknown key",
        ),
        (
            "files = \"cases/*.calc\"\nvariables = { N = 1 }",
            "program[0].variables.N",
            "expected a string",
        ),
        (
            "cases = \"cases/*.toml\"\nvariables = { N = \"1\" }",
            "program[0].variables",
            "states its whole case",
        ),
    ];
    for (entry, key, message) in cases {
        let dir = corpus("pattern-errors", &[], &format!("[[program]]\n{entry}\n"));
        let error = read(&dir).expect_err(entry);
        assert_eq!(error.key, *key, "{entry}: {error}");
        assert!(error.message.contains(message), "{entry}: {error}");
    }
}

/// An id that a listed program or another entry's match also gives is refused, naming both
/// entries; a file two entries match is the same case twice.
#[test]
fn a_matched_id_given_twice_is_refused() {
    let dir = corpus(
        "duplicate-listed",
        &["cases/a.calc"],
        "[[program]]\nid = \"cases/a.calc\"\ntext = \"1\"\n\n[[program]]\nfiles = \"cases/*.calc\"\n",
    );
    assert_error(
        &dir,
        "program \"cases/a.calc\"",
        "duplicate program id: program[0] and program[1].files both give it",
    );
    let dir = corpus(
        "duplicate-matches",
        &["cases/a.calc"],
        "[[program]]\nfiles = \"cases/*.calc\"\n\n[[program]]\nfiles = \"*/a.calc\"\n",
    );
    assert_error(
        &dir,
        "program \"cases/a.calc\"",
        "program[0].files and program[1].files both give it",
    );
    // Two listed programs keep their error.
    let dir = corpus(
        "duplicate-plain",
        &[],
        "[[program]]\nid = \"a\"\ntext = \"1\"\n\n[[program]]\nid = \"a\"\ntext = \"2\"\n",
    );
    assert_error(
        &dir,
        "program \"a\"",
        "duplicate program id: program[0] and program[1] both give it",
    );
}

/// A `cases` match is a case document: its `inputs`, no program text, and the document's name,
/// whose directory its inputs' paths are relative to. Its structural errors are manifest errors
/// naming the program.
#[test]
fn a_case_document_is_the_whole_case() {
    let dir = corpus(
        "case-documents",
        &[],
        "[[program]]\ncases = \"cases/*/case.toml\"\n",
    );
    write(
        &dir.join("cases/boot/case.toml"),
        "[inputs]\nrom = { \"$file\" = \"rom.bin\" }\nn = 1\n",
    );
    write(&dir.join("cases/empty/case.toml"), "");
    let manifest = read(&dir).unwrap();
    let mut inputs = toml::Table::new();
    inputs.insert("rom".into(), toml::toml! { "$file" = "rom.bin" }.into());
    inputs.insert("n".into(), 1.into());
    assert_eq!(
        manifest.programs,
        [
            Program {
                id: "cases/boot/case.toml".into(),
                source: None,
                start_sort: None,
                variables: Vec::new(),
                inputs,
                case: Some("cases/boot/case.toml".into()),
                case_file: None,
                expect: None,
                stop_count: None,
            },
            Program {
                id: "cases/empty/case.toml".into(),
                source: None,
                start_sort: None,
                variables: Vec::new(),
                inputs: toml::Table::new(),
                case: Some("cases/empty/case.toml".into()),
                case_file: None,
                expect: None,
                stop_count: None,
            }
        ]
    );
    let refused = |document: &str, key: &str, message: &str| {
        write(&dir.join("cases/empty/case.toml"), document);
        let error = read(&dir).expect_err(document);
        assert_eq!(error.key, key, "{error}");
        assert!(error.message.contains(message), "{error}");
    };
    let id = "program \"cases/empty/case.toml\"";
    refused("inputs = 3", &format!("{id}.inputs"), "expected a table");
    refused(
        "[inputs]\n\"\" = 1",
        &format!("{id}.inputs."),
        "empty input name",
    );
    refused(
        "program = 1",
        &format!("{id}.program"),
        "a case has the keys `inputs` and `expect`",
    );
    refused("[inputs", id, "no TOML document");

    // A `cases` pattern without a wildcard names one case document.
    write(&dir.join("cases/empty/case.toml"), "");
    write(
        &dir.join("FLOW.toml"),
        &format!("{SPEC}[[program]]\ncases = \"cases/boot/case.toml\"\n"),
    );
    assert_eq!(ids(&read(&dir).unwrap()), ["cases/boot/case.toml"]);
    write(
        &dir.join("FLOW.toml"),
        &format!("{SPEC}[[program]]\ncases = \"cases/gone/case.toml\"\n"),
    );
    assert_error(&dir, "program[0].cases", "matches no file");
}

/// A case document is read inside the manifest's directory: one that resolves outside it through
/// a link is refused.
#[cfg(unix)]
#[test]
fn a_case_document_stays_inside_the_manifest_directory() {
    let dir = corpus(
        "case-escape",
        &[],
        "[[program]]\ncases = \"cases/*.toml\"\n",
    );
    let outside = dir.parent().unwrap().join("case-escape-outside.toml");
    fs::write(&outside, "[inputs]\nn = 1\n").unwrap();
    fs::create_dir_all(dir.join("cases")).unwrap();
    std::os::unix::fs::symlink(&outside, dir.join("cases/out.toml")).unwrap();
    assert_error(
        &dir,
        "program \"cases/out.toml\"",
        "escapes the manifest's directory",
    );
}

/// The definition of kink-flow's `tests/check.rs` typed-input cases: no `$PGM`; `$ENTRY`, `$N`
/// and `$ROM` bound by name.
const CASES_K: &str = "module CASES
  imports INT
  imports BOOL
  imports BYTES
  imports BASIC-K
  syntax KItem ::= \"go\" [symbol(go)]
  configuration <k> $ENTRY:K </k> <n> $N:Int </n> <rom> $ROM:Bytes </rom> <out> 0 </out>
  rule [go]: <k> go => .K ... </k> <n> N </n> <rom> R </rom> <out> _ => N +Int lengthBytes(R) </out>
endmodule
";

/// A test front end's decoder: an input's K name is its name in upper case; an integer is an Int,
/// `{"$file" = path}` the file's bytes, `{"$chain" = [first, second]}` the bytes of `second`
/// named relative to `first`, and `{"$go" = true}` the item `go`.
struct TestDecoder;

impl kink_flow::InputDecoder for TestDecoder {
    fn decode(
        &self,
        name: &str,
        document: &toml::Value,
        files: &mut dyn kink_flow::InputFiles,
    ) -> Result<(String, k_rust::kast::Term), String> {
        let bytes = |bytes: &[u8]| k_rust::kast::Term::Token {
            token: format!(
                "b\"{}\"",
                bytes
                    .iter()
                    .map(|b| format!("\\x{b:02x}"))
                    .collect::<String>()
            ),
            sort: k_rust::kast::Sort::new("Bytes"),
        };
        let term = match document {
            toml::Value::Integer(value) => k_rust::kast::Term::Token {
                token: value.to_string(),
                sort: k_rust::kast::Sort::new("Int"),
            },
            toml::Value::Table(form) if form.len() == 1 => {
                let (tag, value) = form.iter().next().unwrap();
                match (tag.as_str(), value) {
                    ("$file", toml::Value::String(path)) => bytes(&files.read(None, path)?.1),
                    ("$chain", toml::Value::Array(paths)) => {
                        let (first, _) = files.read(None, paths[0].as_str().unwrap())?;
                        bytes(&files.read(Some(&first), paths[1].as_str().unwrap())?.1)
                    }
                    ("$go", _) => k_rust::kast::Term::Apply {
                        label: k_rust::kast::Label::new("go"),
                        arguments: Vec::new(),
                    },
                    _ => return Err(format!("no reading of the form {tag}")),
                }
            }
            _ => return Err("the declared type does not decide this document".into()),
        };
        Ok((name.to_uppercase(), term))
    }
}

fn on_stack<T: Send + 'static>(body: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(kink_corpus::cli::DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap()
}

fn outcomes(admission: &FlowAdmission) -> Vec<(String, Option<(String, String)>)> {
    admission
        .programs
        .iter()
        .map(|p| {
            let refusal = p.outcome.as_ref().err();
            (
                p.id.clone(),
                refusal.map(|r| (r.stage.clone(), r.reason.clone())),
            )
        })
        .collect()
}

/// A case document's inputs name files relative to the document's directory, as `krs run --case`
/// reads them: `cases/a/case.toml`'s `rom.bin` is `cases/a/rom.bin`, not the manifest's
/// `rom.bin`, and a file named from another is relative to that one. Each case's initial
/// configuration is the one its inputs written out as K text give. Read at the K level, without a
/// decoder, each case is refused (`typed-inputs`), as a listed program with `inputs` is.
#[test]
fn case_document_inputs_are_relative_to_the_document() {
    let dir = scratch("case-inputs");
    write(&dir.join("cases.k"), CASES_K);
    fs::write(dir.join("rom.bin"), [0xaa, 0xbb, 0xcc]).unwrap();
    fs::create_dir_all(dir.join("cases/a")).unwrap();
    fs::create_dir_all(dir.join("cases/b/sub")).unwrap();
    fs::write(dir.join("cases/a/rom.bin"), [0x00, 0xff]).unwrap();
    fs::write(dir.join("cases/b/sub/first.bin"), []).unwrap();
    fs::write(dir.join("cases/b/sub/second.bin"), [0x01]).unwrap();
    write(
        &dir.join("cases/a/case.toml"),
        "[inputs]\nentry = { \"$go\" = true }\nn = 1\nrom = { \"$file\" = \"rom.bin\" }\n",
    );
    write(
        &dir.join("cases/b/case.toml"),
        "[inputs]\nentry = { \"$go\" = true }\nn = 2\n\
         rom = { \"$chain\" = [\"sub/first.bin\", \"second.bin\"] }\n",
    );
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "cases.k"
main_module = "CASES"

[[program]]
cases = "cases/*/case.toml"

[[program]]
id = "a-as-text"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "b-as-text"
variables = { ENTRY = "go", N = "2", ROM = 'b"\x01"' }
"#,
    );
    let manifest = read(&dir).unwrap();
    let k_level = manifest.clone();
    let manifest = manifest.with_input_decoder(std::sync::Arc::new(TestDecoder));
    let admission = on_stack(move || admit(&manifest));
    assert_eq!(
        outcomes(&admission),
        [
            ("cases/a/case.toml".to_owned(), None),
            ("cases/b/case.toml".to_owned(), None),
            ("a-as-text".to_owned(), None),
            ("b-as-text".to_owned(), None),
        ]
    );
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap().initial_state.clone()
    };
    assert_eq!(initial("cases/a/case.toml"), initial("a-as-text"));
    assert_eq!(initial("cases/b/case.toml"), initial("b-as-text"));

    let admission = on_stack(move || admit(&k_level));
    let typed = Some(("inputs".to_owned(), "typed-inputs".to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("cases/a/case.toml".to_owned(), typed.clone()),
            ("cases/b/case.toml".to_owned(), typed),
            ("a-as-text".to_owned(), None),
            ("b-as-text".to_owned(), None),
        ]
    );
}

/// A case document reached through a link names its files relative to the directory it was
/// matched in, as `krs run --case cases/a/case.toml` reads them, not relative to the file the
/// link leads to: two links to one document are two cases, each with its own `rom.bin`. A file
/// named from another is relative to that file's name, links resolved.
#[cfg(unix)]
#[test]
fn a_linked_case_document_names_files_beside_the_link() {
    let dir = scratch("case-links");
    write(&dir.join("cases.k"), CASES_K);
    write(
        &dir.join("shared/case.toml"),
        "[inputs]\nentry = { \"$go\" = true }\nn = 1\nrom = { \"$file\" = \"rom.bin\" }\n",
    );
    fs::create_dir_all(dir.join("cases/a")).unwrap();
    fs::create_dir_all(dir.join("cases/b")).unwrap();
    fs::write(dir.join("cases/a/rom.bin"), [0x00, 0xff]).unwrap();
    fs::write(dir.join("cases/b/rom.bin"), [0x01]).unwrap();
    for case in ["a", "b"] {
        std::os::unix::fs::symlink(
            dir.join("shared/case.toml"),
            dir.join(format!("cases/{case}/case.toml")),
        )
        .unwrap();
    }
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "cases.k"
main_module = "CASES"

[[program]]
cases = "cases/*/case.toml"

[[program]]
id = "a-as-text"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "b-as-text"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x01"' }
"#,
    );
    let manifest = read(&dir)
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(TestDecoder));
    assert_eq!(
        manifest.programs[0].case.as_deref(),
        Some("cases/a/case.toml")
    );
    let admission = on_stack(move || admit(&manifest));
    assert_eq!(
        outcomes(&admission),
        [
            ("cases/a/case.toml".to_owned(), None),
            ("cases/b/case.toml".to_owned(), None),
            ("a-as-text".to_owned(), None),
            ("b-as-text".to_owned(), None),
        ]
    );
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap().initial_state.clone()
    };
    assert_eq!(initial("cases/a/case.toml"), initial("a-as-text"));
    assert_eq!(initial("cases/b/case.toml"), initial("b-as-text"));
}

/// A test front end that binds programs as the krs front end binds them to a main parameter
/// that is not `$PGM`: a `.bin` file is the bytes of `$ROM`, as a term; any other file, and
/// inline text, is the text of `$ENTRY`; a file named `bad.*` is refused. Typed inputs are
/// [`TestDecoder`]'s.
struct MainDecoder;

impl kink_flow::InputDecoder for MainDecoder {
    fn decode(
        &self,
        name: &str,
        document: &toml::Value,
        files: &mut dyn kink_flow::InputFiles,
    ) -> Result<(String, k_rust::kast::Term), String> {
        TestDecoder.decode(name, document, files)
    }

    fn program(
        &self,
        name: Option<&str>,
        bytes: &[u8],
    ) -> Option<Result<kink_flow::ProgramBinding, String>> {
        Some(match name {
            Some(name) if name.starts_with("bad.") => Err("no reading of this file".into()),
            Some(name) if name.ends_with(".bin") => Ok(kink_flow::ProgramBinding::Term {
                variable: "ROM".into(),
                term: k_rust::kast::Term::Token {
                    token: format!(
                        "b\"{}\"",
                        bytes
                            .iter()
                            .map(|b| format!("\\x{b:02x}"))
                            .collect::<String>()
                    ),
                    sort: k_rust::kast::Sort::new("Bytes"),
                },
            }),
            _ => Ok(kink_flow::ProgramBinding::Text {
                variable: "$ENTRY".into(),
                text: String::from_utf8(bytes.to_vec()).unwrap(),
            }),
        })
    }
}

/// A front end that knows the definition's main input binds a program to it
/// (`InputDecoder::program`): on a definition without `$PGM`, a file binds `$ENTRY` as text and
/// a binary file binds `$ROM` as a term, and each gives the initial configuration the same
/// values written under `variables` give. The program digest holds the SHA-256 of the program's
/// bytes whichever way they bind, so a program bound as `$PGM` text keeps its digest. A variable
/// the program and `variables` or an input both bind, a start sort beside a binding that is not
/// `$PGM` text, and a program the decoder refuses are refused (`inputs`/`input-value`). Without a
/// decoder the program is `$PGM` text, which this definition refuses (`stray-program`).
#[test]
fn a_front_end_binds_a_program_to_its_main_input() {
    let dir = scratch("program-binding");
    write(&dir.join("cases.k"), CASES_K);
    write(&dir.join("go.txt"), "go");
    write(&dir.join("bad.txt"), "go");
    fs::write(dir.join("rom.bin"), [0x00, 0xff]).unwrap();
    write(
        &dir.join("FLOW.toml"),
        r#"[spec]
entry = "cases.k"
main_module = "CASES"

[[program]]
id = "entry-file"
file = "go.txt"
variables = { N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "entry-text"
text = "go"
variables = { N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "rom-file"
file = "rom.bin"
variables = { ENTRY = "go", N = "1" }

[[program]]
id = "as-text"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "twice-by-variables"
file = "go.txt"
variables = { ENTRY = "go", N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "twice-by-input"
file = "rom.bin"
variables = { ENTRY = "go", N = "1" }
inputs = { rom = { "$file" = "rom.bin" } }

[[program]]
id = "start-sort"
file = "go.txt"
start_sort = "KItem"
variables = { N = "1", ROM = 'b"\x00\xff"' }

[[program]]
id = "refused"
file = "bad.txt"
variables = { N = "1", ROM = 'b"\x00\xff"' }
"#,
    );
    let k_level = read(&dir).unwrap();
    let manifest = k_level
        .clone()
        .with_input_decoder(std::sync::Arc::new(MainDecoder));
    let digests = {
        let manifest = manifest.clone();
        on_stack(move || {
            let (_, admitted) = kink_flow::admit_spec(&manifest);
            let (_, inputs) = admitted.expect("the specification is admitted");
            manifest
                .programs
                .iter()
                .take(3)
                .map(|program| {
                    let read = inputs.read(program).unwrap();
                    (
                        kink_flow::digest::program_payload(program, &read)["program_sha256"]
                            .clone(),
                        read.bound.map(|bound| bound.variable),
                    )
                })
                .collect::<Vec<_>>()
        })
    };
    let sha256 = |bytes: &[u8]| serde_json::json!(kink_patch::sha256(bytes).to_string());
    assert_eq!(
        digests,
        [
            (sha256(b"go"), Some("ENTRY".to_owned())),
            (sha256(b"go"), Some("ENTRY".to_owned())),
            (sha256(&[0x00, 0xff]), Some("ROM".to_owned())),
        ]
    );
    let admission = on_stack(move || admit(&manifest));
    let value = Some(("inputs".to_owned(), "input-value".to_owned()));
    assert_eq!(
        outcomes(&admission),
        [
            ("entry-file".to_owned(), None),
            ("entry-text".to_owned(), None),
            ("rom-file".to_owned(), None),
            ("as-text".to_owned(), None),
            ("twice-by-variables".to_owned(), value.clone()),
            ("twice-by-input".to_owned(), value.clone()),
            ("start-sort".to_owned(), value.clone()),
            ("refused".to_owned(), value),
        ]
    );
    // The configuration variables' values, by variable: the initial configuration's map, whose
    // concatenation follows the binding order, as the set of its bindings.
    fn bindings(pattern: &k_rust::kore::ast::Pattern, into: &mut Vec<String>) {
        match pattern {
            k_rust::kore::ast::Pattern::Application { symbol, arguments }
                if symbol.name.as_str() == "Lbl'Unds'Map'Unds'"
                    || symbol.name.as_str() == "LblinitGeneratedTopCell" =>
            {
                for argument in arguments {
                    bindings(argument, into);
                }
            }
            other => into.push(format!("{other:?}")),
        }
    }
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        let mut found = Vec::new();
        bindings(&program.outcome.as_ref().unwrap().initial_state, &mut found);
        found.sort();
        found
    };
    assert_eq!(initial("as-text").len(), 3);
    assert_eq!(initial("entry-file"), initial("as-text"));
    assert_eq!(initial("entry-text"), initial("as-text"));
    assert_eq!(initial("rom-file"), initial("as-text"));
    let detail = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap_err().detail.clone()
    };
    assert_eq!(
        detail("twice-by-variables"),
        "the program file go.txt binds $ENTRY, which `variables` binds too; bind it once"
    );
    assert_eq!(
        detail("twice-by-input"),
        "input `rom` binds $ROM, which the program binds too; bind it once"
    );
    assert_eq!(
        detail("start-sort"),
        "the program file go.txt binds $ENTRY, and a start_sort reads $PGM text only; give no \
         start_sort"
    );
    assert_eq!(
        detail("refused"),
        "the program file bad.txt: no reading of this file"
    );

    let admission = on_stack(move || admit(&k_level));
    let stray = Some(("inputs".to_owned(), "stray-program".to_owned()));
    let outcomes = outcomes(&admission);
    assert_eq!(outcomes[0], ("entry-file".to_owned(), stray.clone()));
    assert_eq!(outcomes[1], ("entry-text".to_owned(), stray));
}

/// The calc fixture's programs, matched by a pattern in one directory and listed by id in
/// another: `check`, `results` and `run` give the same documents (each program reported by its
/// path id, in the ids' order), and a second command gives the same ids again.
#[test]
fn a_pattern_corpus_is_reported_as_its_listed_programs() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../testdata/flow/calc");
    let make = |name: &str, programs: &str| {
        let dir = scratch(name);
        fs::copy(fixture.join("calc.k"), dir.join("calc.k")).unwrap();
        fs::copy(fixture.join("MUTATIONS.toml"), dir.join("MUTATIONS.toml")).unwrap();
        for program in ["add", "nested", "sub"] {
            fs::create_dir_all(dir.join("cases")).unwrap();
            fs::copy(
                fixture.join(format!("programs/{program}.calc")),
                dir.join(format!("cases/{program}.calc")),
            )
            .unwrap();
        }
        write(
            &dir.join("FLOW.toml"),
            &format!(
                "[spec]\nentry = \"calc.k\"\nmain_module = \"CALC\"\nsyntax_module = \
                 \"CALC-SYNTAX\"\n{programs}"
            ),
        );
        dir
    };
    let pattern = make("report-pattern", "[[program]]\nfiles = \"cases/*.calc\"\n");
    let listed = make(
        "report-listed",
        &["add", "nested", "sub"]
            .map(|p| format!("[[program]]\nid = \"cases/{p}.calc\"\nfile = \"cases/{p}.calc\"\n"))
            .concat(),
    );
    let expected = ["cases/add.calc", "cases/nested.calc", "cases/sub.calc"];
    let documents = |dir: &Path| {
        let manifest = dir.join("FLOW.toml");
        let (check, check_status) = check(&manifest);
        let results_options = ResultsOptions {
            verify: false,
            cache: None,
            mutations: None,
        };
        let (first, results_status) = results(&manifest, &results_options);
        let (again, _) = results(&manifest, &results_options);
        let (run, run_status) = run(
            &manifest,
            &dir.join("MUTATIONS.toml"),
            &RunOptions {
                ..RunOptions::default()
            },
        );
        assert_eq!(program_ids(&check), expected, "{check:#}");
        assert_eq!(program_ids(&first), expected, "{first:#}");
        assert_eq!(program_ids(&again), expected, "{again:#}");
        assert_eq!(program_ids(&run), expected, "{run:#}");
        (
            (check, check_status),
            (first, results_status),
            (run, run_status),
        )
    };
    let (from_pattern, from_list) = (documents(&pattern), documents(&listed));
    let killers = mutation_killers(&from_pattern.2.0);
    assert!(
        killers.iter().any(|k| expected.contains(&k.as_str())),
        "some mutation is killed by a matched program: {killers:?}"
    );
    // Wall-clock times are the host's; every other field must agree.
    let strip = |document: &Value, dir: &Path| {
        let mut document = document.clone();
        without_times(&mut document);
        document
            .to_string()
            .replace(&dir.display().to_string(), "<dir>")
    };
    assert_eq!(
        strip(&from_pattern.0.0, &pattern),
        strip(&from_list.0.0, &listed)
    );
    assert_eq!(from_pattern.0.1, from_list.0.1);
    assert_eq!(
        strip(&from_pattern.1.0, &pattern),
        strip(&from_list.1.0, &listed)
    );
    assert_eq!(
        strip(&from_pattern.2.0, &pattern),
        strip(&from_list.2.0, &listed)
    );
}

/// The ids of a document's `programs` rows (`check`, `results`), or of a run document's corpus
/// (`programs` of its header).
fn program_ids(document: &Value) -> Vec<String> {
    document["programs"]
        .as_array()
        .unwrap_or_else(|| panic!("no programs in {document:#}"))
        .iter()
        .map(|p| p["id"].as_str().unwrap().to_owned())
        .collect()
}

/// Every mutation's killer, where it has one.
fn mutation_killers(document: &Value) -> Vec<String> {
    document["mutations"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|m| m["killer"].as_str().map(str::to_owned))
        .collect()
}

/// `value` with every wall-clock field (a key ending in `_ms`) set to null.
fn without_times(value: &mut Value) {
    match value {
        Value::Object(map) => {
            for (key, field) in map.iter_mut() {
                if key.ends_with("_ms") {
                    *field = Value::Null;
                } else {
                    without_times(field);
                }
            }
        }
        Value::Array(items) => items.iter_mut().for_each(without_times),
        _ => {}
    }
}

/// A case document of named cases: each case of `case` is a program whose id is the document's
/// path, `#` and its name, in document order, an included file's cases at the include's place
/// (`.toml` or `.json`, a path relative to the file that names it), each with the file it is
/// written in and the end it expects. Names are distinct across the includes; a cycle of includes,
/// an empty list, an unnamed case, a key a case does not have and a case's `run` are refused,
/// naming the position.
#[test]
fn named_cases_are_programs_named_by_their_document_and_name() {
    let dir = corpus(
        "named-cases",
        &[],
        "[[program]]\ncases = \"cases/*.toml\"\n",
    );
    write(
        &dir.join("cases/one.toml"),
        "[inputs]\nn = 1\n\n[expect]\nhalt = \"stuck\"\n",
    );
    let document = "[[case]]\nname = \"first\"\ninputs = { n = 2 }\n\n\
                    [[case]]\nname = \"second\"\ninputs = { n = 3 }\nexpect = { halt = \"stuck\" }\n";
    write(
        &dir.join("cases/runs.toml"),
        &format!("{document}\n[[case]]\n\"$data-file\" = \"data/more.json\"\n"),
    );
    write(
        &dir.join("cases/data/more.json"),
        r#"[{"name": "third", "inputs": {"n": 4}, "expect": {"cells": {"n": 4}}},
            {"$data-file": "deeper/last.toml"}]"#,
    );
    write(
        &dir.join("cases/data/deeper/last.toml"),
        "[[case]]\nname = \"fourth\"\ninputs = { n = 5 }\n",
    );
    let manifest = read(&dir).unwrap();
    assert_eq!(
        ids(&manifest),
        [
            "cases/one.toml",
            "cases/runs.toml#first",
            "cases/runs.toml#second",
            "cases/runs.toml#third",
            "cases/runs.toml#fourth",
        ]
    );
    let table = |text: &str| toml::from_str::<toml::Table>(text).unwrap();
    let facts = manifest
        .programs
        .iter()
        .map(|program| {
            (
                program.case.as_deref(),
                program.case_file.as_deref(),
                program.inputs.clone(),
                program.expect.clone(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        facts,
        [
            (
                Some("cases/one.toml"),
                None,
                table("n = 1"),
                Some(table("halt = \"stuck\"")),
            ),
            (Some("cases/runs.toml"), None, table("n = 2"), None),
            (
                Some("cases/runs.toml"),
                None,
                table("n = 3"),
                Some(table("halt = \"stuck\"")),
            ),
            (
                Some("cases/runs.toml"),
                Some("cases/data/more.json"),
                table("n = 4"),
                Some(table("cells = { n = 4 }")),
            ),
            (
                Some("cases/runs.toml"),
                Some("cases/data/deeper/last.toml"),
                table("n = 5"),
                None,
            ),
        ]
    );
    let id = "program \"cases/runs.toml\"";
    let refused = |text: &str, key: &str, message: &str| {
        write(&dir.join("cases/runs.toml"), text);
        let error = read(&dir).expect_err(text);
        assert_eq!(error.key, key, "{error}");
        assert!(error.message.contains(message), "{error}");
    };
    // A case's `run`: in a named case, at the top of a document of named cases, in a document
    // of one case.
    let run = "kink runs every program as the corpus says";
    refused(
        "[[case]]\nname = \"a\"\nrun = { depth = 3 }\n",
        &format!("{id}.case[0].run"),
        run,
    );
    refused(
        &format!("[run]\ndepth = 3\n\n{document}"),
        &format!("{id}.run"),
        run,
    );
    refused("[run]\ndepth = 3\n", &format!("{id}.run"), run);
    // A `run` that holds a stop condition says that kink asks none, wherever it stands.
    let condition = "its `stop_when` is a stop condition, which the corpus states as `[stop] when`";
    refused(
        "[run]\nstop_before = [\"X.a\"]\nstop_when = { function = \"F\", cells = [\"n\"] }\n",
        &format!("{id}.run"),
        condition,
    );
    refused(
        "[[case]]\nname = \"a\"\nrun = { stop_when = { function = \"F\", cells = [\"n\"] } }\n",
        &format!("{id}.case[0].run"),
        condition,
    );
    refused(
        &format!("{document}\n[[case]]\nname = \"first\"\n"),
        &format!("{id}.case[2].name"),
        "`first` is also the name of the case at program \"cases/runs.toml\".case[0]",
    );
    write(
        &dir.join("cases/data/deeper/last.toml"),
        "[[case]]\nname = \"first\"\n",
    );
    refused(
        "[[case]]\nname = \"first\"\n\n[[case]]\n\"$data-file\" = \"data/more.json\"\n",
        &format!("{id}.case[1]$data-file(data/more.json)[1]$data-file(deeper/last.toml)[0].name"),
        "also the name",
    );
    write(
        &dir.join("cases/data/deeper/last.toml"),
        "case = { \"$data-file\" = \"../more.json\" }\n",
    );
    refused(
        "case = { \"$data-file\" = \"data/more.json\" }\n",
        &format!("{id}.case$data-file(data/more.json)[1]$data-file(deeper/last.toml)"),
        "`cases/data/more.json` includes `cases/data/deeper/last.toml` includes \
         `cases/data/more.json`",
    );
    refused("case = []\n", &format!("{id}.case"), "lists no case");
    refused(
        "[[case]]\ninputs = { n = 1 }\n",
        &format!("{id}.case[0]"),
        "has a `name`",
    );
    refused(
        "[[case]]\nname = \"a\"\nfile = \"x\"\n",
        &format!("{id}.case[0].file"),
        "it has the keys `name`, `inputs` and `expect`",
    );
    refused(
        "[[case]]\nname = \"a\"\nexpect = 1\n",
        &format!("{id}.case[0].expect"),
        "expected a table",
    );
    refused(
        "[[case]]\n\"$file\" = \"x\"\n",
        &format!("{id}.case[0]"),
        "`$file` is no case",
    );
    refused(
        "name = \"a\"\n",
        &format!("{id}.name"),
        "a document of one case names none",
    );
    write(
        &dir.join("cases/data/null.json"),
        r#"[{"name": "a", "inputs": {"n": null}}]"#,
    );
    refused(
        "case = { \"$data-file\" = \"data/null.json\" }\n",
        &format!("{id}.case"),
        "`$data-file` `cases/data/null.json`",
    );
}

/// A case's expectation is read by the front end that reads the definition's ends: without one
/// (here a K-level manifest with a decoder of typed inputs but no renderer of ends) the case is
/// refused at stage `inputs`, reason `typed-expectation`, as typed inputs are without a decoder,
/// and a case without an expectation is admitted.
#[test]
fn an_expectation_needs_a_front_end_that_reads_ends() {
    let dir = scratch("expect-k-level");
    write(&dir.join("cases.k"), CASES_K);
    fs::create_dir_all(dir.join("cases/data")).unwrap();
    fs::write(dir.join("cases/data/rom.bin"), [0x07]).unwrap();
    write(
        &dir.join("cases/runs.toml"),
        "[[case]]\nname = \"plain\"\ninputs = { entry = { \"$go\" = true }, n = 1, rom = { \"$file\" = \"data/rom.bin\" } }\n\n\
         [[case]]\nname = \"expecting\"\ninputs = { entry = { \"$go\" = true }, n = 2, rom = { \"$file\" = \"data/rom.bin\" } }\n\
         expect = { halt = \"stuck\" }\n\n\
         [[case]]\n\"$data-file\" = \"data/more.toml\"\n",
    );
    // An included case's paths are relative to its file.
    fs::write(dir.join("cases/data/data.bin"), [0x01, 0x02]).unwrap();
    write(
        &dir.join("cases/data/more.toml"),
        "[[case]]\nname = \"included\"\ninputs = { entry = { \"$go\" = true }, n = 3, rom = { \"$file\" = \"data.bin\" } }\n",
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"cases.k\"\nmain_module = \"CASES\"\n\n[[program]]\ncases = \"cases/*.toml\"\n\n\
         [[program]]\nid = \"included-as-text\"\nvariables = { ENTRY = \"go\", N = \"3\", ROM = 'b\"\\x01\\x02\"' }\n",
    );
    let manifest = read(&dir)
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(TestDecoder));
    let admission = on_stack(move || admit(&manifest));
    assert_eq!(
        outcomes(&admission),
        [
            ("cases/runs.toml#plain".to_owned(), None),
            (
                "cases/runs.toml#expecting".to_owned(),
                Some(("inputs".to_owned(), "typed-expectation".to_owned()))
            ),
            ("cases/runs.toml#included".to_owned(), None),
            ("included-as-text".to_owned(), None),
        ]
    );
    let initial = |id: &str| {
        let program = admission.programs.iter().find(|p| p.id == id).unwrap();
        program.outcome.as_ref().unwrap().initial_state.clone()
    };
    assert_eq!(
        initial("cases/runs.toml#included"),
        initial("included-as-text")
    );
}

/// A test front end's renderer of ends: it shows no kill, refuses an expectation with the key
/// `bad`, and meets an expectation exactly when it states the count of the baseline's ends
/// (`ends = N`), saying under `[stop]` that it did not compare a halt.
struct TestRenderer;

impl kink_flow::EndRenderer for TestRenderer {
    fn format(&self) -> &'static str {
        "test/1"
    }

    fn identity(&self) -> Result<Value, String> {
        Ok(Value::Null)
    }

    fn difference(
        &self,
        _: &std::collections::BTreeSet<k_rust::kore::ast::Pattern>,
        _: &std::collections::BTreeSet<k_rust::kore::ast::Pattern>,
        _: bool,
        _: &[String],
    ) -> Result<Value, String> {
        Err("the test renderer shows no kill".into())
    }

    fn read_expectation(
        &self,
        expect: &toml::Table,
        _: &mut dyn kink_flow::InputFiles,
    ) -> Result<(), String> {
        if expect.contains_key("bad") {
            return Err("`bad` is no part of an expectation".into());
        }
        Ok(())
    }

    fn check_expectation(
        &self,
        check: kink_flow::ExpectationCheck<'_>,
    ) -> Result<kink_flow::CheckedExpectation, String> {
        let stated = check.expect["ends"].as_integer().unwrap();
        let met = usize::try_from(stated).unwrap() == check.ends.len();
        Ok(kink_flow::CheckedExpectation {
            verdict: if met {
                kink_flow::ExpectationVerdict::Met
            } else {
                kink_flow::ExpectationVerdict::Unmet
            },
            detail: check.stop.map(|_| "no halt compared".to_owned()),
            difference: (!met)
                .then(|| serde_json::json!({"format": "test/1", "ends": check.ends.len()})),
        })
    }
}

/// With a front end's renderer, each case's expectation is checked against its baseline's ends
/// and reported in its row of `results`, `run` and `check` (`check` reads the current result
/// record), and decides no verdict: an unmet expectation leaves `results` and `check` ok. Only
/// `results`, which asks whether each baseline meets its expectation, exits by it: 1 for the
/// unmet one.
/// A program whose expectation the renderer refuses is refused (`inputs`/`expectation-value`),
/// and so is its expectation's report inconclusive. A program without `expect` has no
/// `expectation`.
#[test]
fn a_case_expectation_is_checked_by_the_front_ends_renderer() {
    let dir = scratch("expect-renderer");
    write(&dir.join("cases.k"), CASES_K);
    fs::create_dir_all(dir.join("cases")).unwrap();
    fs::write(dir.join("cases/rom.bin"), [0x07]).unwrap();
    let case = |name: &str, n: u8, expect: &str| {
        format!(
            "[[case]]\nname = \"{name}\"\ninputs = {{ entry = {{ \"$go\" = true }}, n = {n}, rom = {{ \"$file\" = \"rom.bin\" }} }}\n{expect}\n"
        )
    };
    write(
        &dir.join("cases/runs.toml"),
        &[
            case("met", 1, "expect = { ends = 1 }"),
            case("unmet", 2, "expect = { ends = 2 }"),
            case("none", 3, ""),
        ]
        .concat(),
    );
    write(
        &dir.join("FLOW.toml"),
        "[spec]\nentry = \"cases.k\"\nmain_module = \"CASES\"\n\n[[program]]\ncases = \"cases/*.toml\"\n",
    );
    let manifest = read(&dir)
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(TestDecoder))
        .with_end_renderer(std::sync::Arc::new(TestRenderer));
    let expectations = |document: &Value| {
        document["programs"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                (
                    row["id"].as_str().unwrap().to_owned(),
                    row.get("expectation").cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let met = serde_json::json!({"verdict": "met", "detail": null, "difference": null});
    let unmet = serde_json::json!({
        "verdict": "unmet",
        "detail": null,
        "difference": {"format": "test/1", "ends": 1},
    });
    let reported = [
        ("cases/runs.toml#met".to_owned(), Some(met)),
        ("cases/runs.toml#unmet".to_owned(), Some(unmet)),
        ("cases/runs.toml#none".to_owned(), None),
    ];
    let checking = manifest.clone();
    let (results, results_ok) =
        on_stack(move || kink_flow::results::results(&manifest, &ResultsOptions::default()));
    assert!(results_ok, "{results:#}");
    assert_eq!(expectations(&results), reported, "{results:#}");
    assert_eq!(
        kink_flow::cli::results_status(&results),
        kink_flow::cli::EXIT_NO,
        "{results:#}"
    );
    let (check, status) = on_stack(move || {
        kink_flow::cli::run_command(
            &checking,
            &kink_flow::FlowCommand::Check(kink_flow::cli::CheckOptions::default()),
            &kink_flow::FrontEnd::default(),
        )
    });
    assert_eq!(status, kink_flow::cli::EXIT_YES, "{check:#}");
    assert_eq!(check["version"], 12, "{check:#}");
    assert_eq!(expectations(&check), reported, "{check:#}");

    // A refused expectation refuses its case.
    write(
        &dir.join("cases/runs.toml"),
        &case("bad", 1, "expect = { bad = 1 }"),
    );
    let manifest = read(&dir)
        .unwrap()
        .with_input_decoder(std::sync::Arc::new(TestDecoder))
        .with_end_renderer(std::sync::Arc::new(TestRenderer));
    let (check, status) = on_stack(move || {
        kink_flow::cli::run_command(
            &manifest,
            &kink_flow::FlowCommand::Check(kink_flow::cli::CheckOptions::default()),
            &kink_flow::FrontEnd::default(),
        )
    });
    assert_eq!(status, kink_flow::cli::EXIT_UNASKED, "{check:#}");
    let row = &check["programs"][0];
    assert_eq!(
        (&row["outcome"], &row["stage"], &row["reason"]),
        (
            &Value::from("refused"),
            &Value::from("inputs"),
            &Value::from("expectation-value")
        ),
        "{check:#}"
    );
    assert_eq!(
        row["detail"], "expect: `bad` is no part of an expectation",
        "{check:#}"
    );
    assert_eq!(row["expectation"]["verdict"], "inconclusive", "{check:#}");
}
