//! A print groups a child that priority or associativity forbids bare with the definition's own
//! bracket. A program never needs such a bracket as parsed (the parser read it bare), but
//! printing reverses aliases, which can move a child under a production that binds tighter than
//! it; where the definition declares no bracket that takes it, a reversal that cannot read back
//! is not done, and the term prints unreversed. Only a term no text of the definition writes (a
//! rule built it) is printed with a stated fallback.
//!
//! One package generated from a table of relations: for each relation a precedence or an
//! associativity declares (`a` over `b`, `left`, `right`, `non_assoc`), infix alias productions
//! of their own call forms, in a sort with a bracket (`Pb`) and in one without (`Pn`). A program
//! writes the call forms, which parse alone; each is printed by `krs parse --output program` (the
//! program grammar's text) and by `krs run` (a configuration value's), and `krs prove` prints a
//! claim's leaf. Every command runs with `KRS_CHECK_PRINTS=1`, so each print that claims to be
//! the term is read back as it ([`krs_test_support::CHECK_PRINTS`]).

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

/// The relations: the alias productions' group declaration, and each production's letter.
const RELATIONS: [(&str, &str, &[char]); 4] = [
    ("Prio", "(A) > (B)", &['a', 'b']),
    ("Left", "left (L)", &['l']),
    ("Right", "right (R)", &['r']),
    ("NonAssoc", "non_assoc (N)", &['n']),
];

/// Each pair a relation orders: the program in the call forms of a family (`F` its prefix), and
/// the infix print with every grouping the relation requires as the definition's bracket
/// `(..)` writes it.
const PAIRS: [(&str, &str); 9] = [
    ("Fa(Fb(1, 2), 3)", "(1 b 2) a 3"),
    ("Fa(1, Fb(2, 3))", "1 a (2 b 3)"),
    ("Fb(Fa(1, 2), 3)", "1 a 2 b 3"),
    ("Fl(1, Fl(2, 3))", "1 l (2 l 3)"),
    ("Fl(Fl(1, 2), 3)", "1 l 2 l 3"),
    ("Fr(Fr(1, 2), 3)", "(1 r 2) r 3"),
    ("Fr(1, Fr(2, 3))", "1 r 2 r 3"),
    ("Fn(Fn(1, 2), 3)", "(1 n 2) n 3"),
    ("Fn(1, Fn(2, 3))", "1 n (2 n 3)"),
];

/// The library: a family per sort, `Pb` with the bracket `(..)` and `Pn` without.
fn library() -> String {
    let mut source = String::from(
        "use k::builtin::{Int, KSequence};\nuse k::{KResult, Term};\n\nk::sorts! {\n    Stmt: KResult;\n}\n",
    );
    for (family, bracket) in [("Pb", true), ("Pn", false)] {
        let prefix = family.to_lowercase();
        let bracket = if bracket {
            "#[k::bracket(\"({value})\")]\n"
        } else {
            ""
        };
        let _ = write!(
            source,
            "\n#[k::sort(alias = {family}, parents = [KResult])]\n{bracket}pub trait {family}Sort: k::KResultSort {{}}\npub type {family} = Term<dyn {family}Sort>;\n\n#[k::subsort(sort = {family})]\nimpl {family}Sort for Int {{}}\n\n#[k::constructors(sort = {family}, result = KResult)]\n#[rustfmt::skip]\npub enum {family}Call {{\n"
        );
        for letter in RELATIONS.iter().flat_map(|(_, _, letters)| letters.iter()) {
            let variant = letter.to_ascii_uppercase();
            let _ = writeln!(
                source,
                "    #[k::syntax(\"{prefix}{letter}({{l}}, {{r}})\")] {variant} {{ l: {family}, r: {family} }},"
            );
        }
        source.push_str("}\n");
        for (relation, groups, letters) in RELATIONS {
            let _ = write!(
                source,
                "\n#[k::constructors(sort = {family}, result = KResult)]\n#[k::precedence({groups})]\n#[rustfmt::skip]\npub enum {family}{relation} {{\n"
            );
            for letter in letters {
                let variant = letter.to_ascii_uppercase();
                let _ = writeln!(
                    source,
                    "    #[k::syntax(\"{{l}} {letter} {{r}}\")] #[k::alias] {variant} {{ l: {family}, r: {family} }},"
                );
            }
            source.push_str("}\n");
            for letter in letters {
                let variant = letter.to_ascii_uppercase();
                let _ = write!(
                    source,
                    "\n#[k::alias]\nfn {prefix}_{letter}(k::term![{family}{relation}::{variant}(l, r)]: Term<{family}>) -> Term<{family}> {{\n    {family}Call::{variant}(l, r)\n}}\n"
                );
            }
        }
    }
    source.push_str(
        r#"
/// Infix productions of `Pn` that are no aliases: a rule can build `X(Y(1, 2), 3)`, which no
/// text writes.
#[k::constructors(sort = Pn, result = KResult)]
#[k::precedence((X) > (Y))]
#[rustfmt::skip]
pub enum PnBuilt {
    #[k::syntax("{l} x {r}")] X { l: Pn, r: Pn },
    #[k::syntax("{l} y {r}")] Y { l: Pn, r: Pn },
}

#[k::constructors(sort = Stmt, result = KResult)]
#[rustfmt::skip]
pub enum Program {
    #[k::syntax("pb({x})")] PbStmt { x: Pb },
    #[k::syntax("pn({x})")] PnStmt { x: Pn },
    #[k::syntax("build")] Build {},
}

k::rules! {
    for Stmt;
    use Program::*;

    build: Build {} => PnStmt(PnBuilt::X(PnBuilt::Y(1, 2), 3));
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm] }
    }
}

k::claims! {
    for Machine;
    use Program::*;

    /// No rule rewrites a program, so the leaf is the program.
    #[k::claim(all_paths)]
    stays: {
        k: [PnStmt(PnCall::A(PnCall::B(1, 2), 3))],
    } => {
        k: [],
    };
}
"#,
    );
    source
}

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

fn package(root: &Path) -> PathBuf {
    fs::create_dir_all(root.join("src")).unwrap();
    fs::write(root.join("src/lib.rs"), library()).unwrap();
    let manifest = root.join("Cargo.toml");
    fs::write(
        &manifest,
        format!(
            "[package]\nname = \"brackets\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-BRACKET-PRINTS\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    manifest
}

/// `krs <command>` on the package's `main` definition, with `input` as FILE: whether it passed,
/// its stdout and its stderr.
fn krs(
    target: &Path,
    manifest: &Path,
    command: &str,
    input: Option<&Path>,
) -> (bool, String, String) {
    let mut process = krs_command!();
    fixture_build_env(&mut process, target);
    process
        .args([command, "--manifest-path"])
        .arg(manifest)
        .args(["--package", "brackets", "--definition", "main"]);
    if command == "parse" {
        process.args(["--output", "program"]);
    }
    if let Some(input) = input {
        process.arg(input);
    }
    let output = process
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

/// The `warning:` lines of `stderr`.
fn warnings(stderr: &str) -> Vec<&str> {
    stderr
        .lines()
        .filter(|line| line.starts_with("warning:"))
        .collect()
}

const GROUPED: &str = "warning: priority, associativity or a sort requires a bracket around a child of sort `Pn`, and the definition declares no bracket that takes it: grouped in K's default bracket `( .. )`, which neither a program nor a configuration value reads";

/// Each pair, in each family: with a bracket, both commands group the child in it and the print
/// reads back; without one, the print through the aliases would need a bracket no production
/// declares, so both commands print the call forms the program wrote, which read back, and say
/// nothing. A pair that needs no grouping prints through the aliases in both. A term no text
/// writes, which a rule built, is printed grouped in K's default bracket and says so; its other
/// parts are still read back.
#[test]
fn a_child_that_needs_a_bracket_is_grouped_by_the_definitions_or_printed_unreversed() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(&temporary.path().join("brackets"));
    let (checked, _, stderr) = krs(target.path(), &manifest, "check", None);
    assert!(checked, "{stderr}");
    let program = temporary.path().join("program.txt");
    for (written, grouped) in PAIRS {
        let needs = grouped.contains('(');
        for family in ["pb", "pn"] {
            let call = written.replace('F', family);
            let text = format!("{family}({call})\n");
            fs::write(&program, &text).unwrap();
            let (parsed, printed, parse_stderr) =
                krs(target.path(), &manifest, "parse", Some(&program));
            let (ran, state, run_stderr) = krs(target.path(), &manifest, "run", Some(&program));
            assert!(parsed, "{text}{parse_stderr}");
            assert!(ran, "{text}{state}{run_stderr}");
            let state = state
                .lines()
                .map(str::trim)
                .find(|line| line.ends_with("~> .K"))
                .unwrap_or_else(|| panic!("{text}{state}"));
            let expected = if family == "pb" || !needs {
                grouped
            } else {
                &call
            };
            assert_eq!(
                (printed.trim_end(), warnings(&parse_stderr)),
                (format!("{family}({expected})").as_str(), vec![]),
                "{text}"
            );
            assert_eq!(
                (state, warnings(&run_stderr)),
                (format!("{family}({expected}) ~> .K").as_str(), vec![]),
                "{text}"
            );
        }
    }
    fs::write(&program, "build\n").unwrap();
    let (ran, state, stderr) = krs(target.path(), &manifest, "run", Some(&program));
    assert!(ran, "{state}{stderr}");
    assert!(state.contains("pn(( 1 y 2 ) x 3) ~> .K"), "{state}");
    assert_eq!(warnings(&stderr), [GROUPED], "{stderr}");
    // A leaf is a printed state, as a run's is: the print through the aliases would group a
    // child in K's default bracket, so the leaf prints unreversed.
    let (proven, leaves, stderr) = krs(target.path(), &manifest, "prove", None);
    assert!(!proven, "{leaves}");
    assert!(leaves.contains("pn(pna(pnb(1, 2), 3)) ~> .K"), "{leaves}");
    assert_eq!(warnings(&stderr), Vec::<&str>::new(), "{stderr}");
}
