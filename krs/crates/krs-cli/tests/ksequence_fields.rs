//! A declaration over `KSequence`, K's `K`, emits a production whose module
//! declares the sort: a constructor field and a function parameter or result
//! of type `KSequence` make their module import `SORT-K`, and every route
//! accepts the definition. A rule matches a saved
//! sequence and splices it back into the computation.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const SOURCE: &str = r#"
use k::KResult;
use k::Term;
use k::builtin::{Int, KSequence, List};

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
#[k::precedence(cmd (Park, Resume, Bump, Report, WrapK) > right seq (Seq))]
pub enum Cmd {
    #[k::syntax("park")]
    Park(),
    #[k::syntax("resume")]
    Resume(),
    #[k::syntax("bump")]
    Bump(),
    #[k::syntax("report")]
    Report(),
    #[k::syntax("wrapk ( {body} )")]
    WrapK { body: KSequence },
    #[k::syntax("{first} ; {second}")]
    Seq { first: Stmt, second: Stmt },
}

#[k::function(partial, internal)]
pub fn Body(w: Term<Stmt>) -> Term<KSequence>;

#[k::function(total, internal)]
pub fn Again(b: Term<KSequence>) -> Term<Stmt>;

#[k::equation]
fn body(k::term![Body(Cmd::WrapK(b))]: Term<KSequence>) -> Term<KSequence> {
    b
}

#[k::equation]
fn again(k::term![Again(b)]: Term<Stmt>) -> Term<Stmt> {
    Cmd::WrapK(b)
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub stack: List,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(
        #[k::config_var(name = "PGM", main)] pgm: Stmt,
        #[k::config_var(name = "ACC")] acc: Int,
    ) -> Self {
        Self {
            k: k::k![pgm],
            stack: k::builtin::list::empty(),
            acc,
        }
    }
}

// Saving the rest of the computation has no KRS surface yet.
k::raw_k!(
    r"rule <k> park ~> T:K => bump ~> resume </k> <stack> S:List => ListItem(wrapk(T)) S </stack>"
);

k::rules! {
    for Stmt;
    use Cmd::*;

    seq: Seq(s1, s2) => k::k![s1, s2];
}

k::rules! {
    for Machine;
    use Cmd::*;

    bump: { k: [Bump(), ..], acc: a } => { k: [..], acc: a + 1 };
    report: { k: [Report(), ..], acc: a } => { k: [..], acc: a * 10 };
    resume: { k: [Resume(), ..], stack: [WrapK { body: b }, s @ ..] } => { k: [b, ..], stack: s };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace whose library is `source`.
fn package(root: &Path, name: &str, source: &str) -> PathBuf {
    let directory = root.join(name);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), source).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-CONTINUATIONS\"\nallow-raw-k = true\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package's `main` definition.
fn krs(target: &Path, manifest: &Path, command: &str, extra: &[&str]) -> (bool, String, String) {
    let package = manifest
        .parent()
        .and_then(Path::file_name)
        .and_then(|name| name.to_str())
        .unwrap();
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    let output = process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", package, "--definition", "main"])
        .args(extra)
        .env("NO_COLOR", "1")
        .env("KRS_STAGE_CACHE_DIR", target.join("stages"))
        .output()
        .unwrap();
    (
        output.status.success(),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// The `imports` lines of the emitted module `name`.
fn imports(definition: &str, name: &str) -> Vec<String> {
    let start = definition
        .find(&format!("module {name}\n"))
        .unwrap_or_else(|| panic!("no module {name}:\n{definition}"));
    definition[start..]
        .lines()
        .skip(1)
        .take_while(|line| *line != "endmodule")
        .filter_map(|line| line.trim().strip_prefix("imports "))
        .map(str::to_owned)
        .collect()
}

/// Both modules that declare productions over `K` import `SORT-K`, every
/// route checks the definition, and a computation saved in a `KSequence`
/// field runs when a rule splices it back.
#[test]
fn a_ksequence_declaration_imports_the_sort_k_module() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(temporary.path(), "continuations", SOURCE);
    let (success, _, stderr) = krs(target.path(), &manifest, "check", &[]);
    assert!(success, "{stderr}");

    let output = manifest.with_file_name("emitted");
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    let definition = fs::read_to_string(output.join("definition.k")).unwrap();
    for line in [
        "syntax Stmt ::= \"wrapk\" \"(\" K \")\"",
        "syntax K ::= \"body\" \"(\" Stmt \")\"",
        "syntax Stmt ::= \"again\" \"(\" K \")\"",
    ] {
        assert!(definition.contains(line), "{line}:\n{definition}");
    }
    assert!(
        imports(&definition, "ORG-KRS-CONTINUATIONS-SYNTAX").contains(&"SORT-K".to_owned()),
        "{definition}"
    );
    assert!(
        imports(&definition, "ORG-KRS-CONTINUATIONS").contains(&"SORT-K".to_owned()),
        "{definition}"
    );

    let program = manifest.with_file_name("program.txt");
    fs::write(&program, "park ; report").unwrap();
    let (_, stdout, stderr) = krs(
        target.path(),
        &manifest,
        "run",
        &[program.to_str().unwrap(), "-c", "ACC=0"],
    );
    let flat = stdout.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("<k> .K </k> <stack> .List </stack> <acc> 10 </acc>"),
        "{stdout}\n{stderr}"
    );
}

/// A definition whose `Cmd` enum carries `variant` and whose library ends
/// with `item`, around one computation cell.
fn strict_source(variant: &str, item: &str) -> String {
    format!(
        r#"
use k::KResult;
use k::Term;
use k::builtin::{{Int, KSequence}};

k::sorts! {{
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum Cmd {{
    #[k::syntax("skip")]
    Skip(),
    {variant}
}}
{item}
#[k::configuration]
pub struct Machine {{
    #[k::cell]
    pub k: KSequence,
}}

impl Machine {{
    #[k::init]
    pub fn init(#[k::config_var(name = "PGM", main)] pgm: Stmt) -> Self {{
        Self {{ k: k::k![pgm] }}
    }}
}}
"#
    )
}

/// The `error[..]` lines `krs check` prints, each followed by ` @ ` and the
/// `src/lib.rs:LINE:COLUMN` its `-->` line names, and whether it succeeded.
fn check_errors(target: &Path, manifest: &Path) -> (bool, Vec<String>) {
    let (success, _, stderr) = krs(target, manifest, "check", &[]);
    let lines = stderr.lines().collect::<Vec<_>>();
    let errors = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.starts_with("error"))
        .map(|(index, line)| {
            let location = lines
                .get(index + 1)
                .and_then(|next| next.trim_start().strip_prefix("--> "))
                .map_or("no location", |path| {
                    path.find("src/lib.rs").map_or(path, |start| &path[start..])
                });
            format!("{line} @ {location}")
        })
        .collect();
    (success, errors)
}

/// The `src/lib.rs:LINE:COLUMN` location of `needle`, the first occurrence
/// inside the first occurrence of `anchor` in `source`.
fn location_in(source: &str, anchor: &str, needle: &str) -> String {
    let start = source.find(anchor).expect("the anchor is in the source");
    let at = start + anchor.find(needle).expect("the needle is in the anchor");
    let before = &source[..at];
    let line = before.matches('\n').count() + 1;
    let column = before.len() - before.rfind('\n').map_or(0, |newline| newline + 1) + 1;
    format!("src/lib.rs:{line}:{column}")
}

/// Heating moves the argument at a strict position to the front of the
/// computation as one item, and a `KSequence` value is a sequence of items,
/// so a strict position of sort `KSequence` has no heating step: `krs check`
/// refuses it at the position, on an enum variant's field list and on a
/// constructor struct's `sequence`, naming the position and the reason,
/// instead of handing k-rust a production it cannot heat; a context whose
/// hole has sort `KSequence` is refused at its `hole` key for the same reason.
/// A strict position of an ordinary sort beside a `KSequence` field is
/// accepted.
#[test]
fn a_strict_position_or_a_context_hole_of_sort_ksequence_is_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let reason = |position: &str, production: &str| {
        format!(
            "error[krs::analysis::invalid-strictness]: the strict position `{position}` of `{production}` has sort `KSequence`: heating moves the argument at a strict position to the front of the computation as one item, and a `KSequence` is a sequence of items, so the position has no heating step; give the field a sort of single items, such as `k::KItem` or a declared sort, or leave it out of the strictness"
        )
    };
    let variant = strict_source(
        r#"#[k::syntax("when ( {guard} , {body} )")] #[k::strict(body)]
    When { guard: Stmt, body: KSequence },"#,
        "",
    );
    let structure = strict_source(
        "",
        r#"
#[k::constructor(sort = Stmt, syntax = "loop ( {body} )")]
#[k::seqstrict(sequence = [body], result = KResult)]
pub struct Loop {
    pub body: Term<KSequence>,
}
"#,
    );
    let context = strict_source(
        r#"#[k::syntax("when ( {guard} , {body} )")]
    When { guard: Stmt, body: KSequence },"#,
        r"
#[k::context(hole = h)]
fn when_body(k::term![Cmd::When(_g, h)]: Term<Stmt>) {}
",
    );
    let ordinary = strict_source(
        r#"#[k::syntax("when ( {guard} , {body} )")] #[k::strict(guard)]
    When { guard: Stmt, body: KSequence },"#,
        "",
    );
    for (name, source, expected) in [
        (
            "strict-ksequence-variant",
            &variant,
            vec![format!(
                "{} @ {}",
                reason("body", "When"),
                location_in(&variant, "#[k::strict(body)]", "body")
            )],
        ),
        (
            "strict-ksequence-struct",
            &structure,
            vec![format!(
                "{} @ {}",
                reason("body", "Loop"),
                location_in(&structure, "sequence = [body]", "body")
            )],
        ),
        (
            "context-ksequence-hole",
            &context,
            vec![format!(
                "error[krs::analysis::invalid-context]: the hole `h` of a context has sort `KSequence`: a context moves its hole to the front of the computation as one item, and a `KSequence` is a sequence of items, so the context has no heating step; name a subterm of a sort of single items @ {}",
                location_in(&context, "= h)]\nfn when_body", "h")
            )],
        ),
    ] {
        let manifest = package(temporary.path(), name, source);
        let (success, errors) = check_errors(target.path(), &manifest);
        assert!(!success, "{name}");
        assert_eq!(errors, expected, "{name}");
    }
    let manifest = package(temporary.path(), "strict-ordinary", &ordinary);
    let (success, errors) = check_errors(target.path(), &manifest);
    assert!(success, "{errors:?}");
    assert!(errors.is_empty(), "{errors:?}");
}
