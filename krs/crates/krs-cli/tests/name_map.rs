//! The map from an author's Rust names to the emitted K names: every name rustc accepts either
//! becomes a K name that means what the Rust name means, distinct from every other name of its
//! K namespace, or is refused with an author code whose reason names both Rust names.

use std::fs;
use std::path::{Path, PathBuf};

use krs_test_support::{fixture_build_env, krs_command, shared_fixture_target, temp_dir};

const LIBRARY: &str = r#"use k::KResult;
use k::builtin::{Int, KSequence, int};
use k::Term;

k::sorts! {
    Stmt;
    Value: Stmt + KResult;
    impl Value for Int;
}

#[k::constructors(sort = Stmt, result = KResult)]
pub enum StmtSyntax {
    #[k::syntax("skip")]
    Skip(),
    #[k::syntax("wrap({s})")]
    Wrap { s: Stmt },
}

#[k::configuration]
pub struct Machine {
    #[k::cell]
    pub k: KSequence,
    #[k::cell]
    pub acc: Int,
}

impl Machine {
    #[k::init]
    pub fn init(pgm: Stmt) -> Self {
        Self { k: k::k![pgm], acc: 0 }
    }
}

#[k::function(total, internal)]
pub fn PickF(b: Term<Int>) -> Term<Int>;

k::equations! {
    for PickF;
    table: (b) => int::add(b, 1);
}

k::rules! {
    for Machine;
    use StmtSyntax::*;
    unwrap: { k: [Wrap { s }, ..], acc: v } => { k: [s, ..], acc: PickF(v) };
}
"#;

fn krs_path() -> String {
    let krs = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../krs")
        .canonicalize()
        .unwrap();
    serde_json::to_string(krs.to_str().unwrap()).unwrap()
}

/// Writes a one-package workspace named `name`, in the directory `directory`, whose library is
/// `library`.
fn package(root: &Path, directory: &str, name: &str, library: &str) -> PathBuf {
    let directory = root.join(directory);
    fs::create_dir_all(directory.join("src")).unwrap();
    fs::write(directory.join("src/lib.rs"), library).unwrap();
    fs::write(
        directory.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n[dependencies]\nk = {{ package = \"krs\", path = {} }}\n\n[package.metadata.krs]\nk-namespace = \"ORG-KRS-NAME-MAP\"\n\n[package.metadata.krs.definitions.main]\n\n[workspace]\nresolver = \"3\"\n",
            krs_path(),
        ),
    )
    .unwrap();
    directory.join("Cargo.toml")
}

/// Runs `krs <command>` on the package `package`'s `main` definition.
fn krs(
    target: &Path,
    manifest: &Path,
    package: &str,
    command: &str,
    extra: &[&str],
) -> (bool, String, String) {
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

/// The emitted `definition.k` without its header line and the package-relative source comments,
/// which name the package.
fn emitted_k(target: &Path, manifest: &Path, package: &str, output: &Path) -> String {
    let (success, _, stderr) = krs(
        target,
        manifest,
        package,
        "emit-k",
        &["--output", output.to_str().unwrap()],
    );
    assert!(success, "{stderr}");
    fs::read_to_string(output.join("definition.k"))
        .unwrap()
        .lines()
        .skip(1)
        .filter(|line| !line.trim_start().starts_with("// KRS "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// A package whose name is a Rust keyword is a crate rustc names by the raw identifier
/// (`module_path!()` writes `r#let`), which is the identifier `let`: its items are the selected
/// target's, so it checks, and its K is the K of the same library under another name.
#[test]
fn a_package_named_by_a_keyword_is_its_crate() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let keyword = package(temporary.path(), "keyword", "let", LIBRARY);
    let plain = package(temporary.path(), "plain", "name_map_plain", LIBRARY);
    let (success, _, stderr) = krs(target.path(), &keyword, "let", "check", &[]);
    assert!(success, "{stderr}");
    assert_eq!(
        emitted_k(
            target.path(),
            &keyword,
            "let",
            &temporary.path().join("keyword-out")
        ),
        emitted_k(
            target.path(),
            &plain,
            "name_map_plain",
            &temporary.path().join("plain-out")
        ),
    );
}

/// A raw identifier is the identifier itself, so a table row written `r#table` is the row `table`
/// (its K is the plain row's), and one written `r#match` is the row `match`, labelled by it.
#[test]
fn a_raw_row_name_is_its_identifier() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let plain = package(temporary.path(), "plain", "name_map_rows", LIBRARY);
    let raw = package(
        temporary.path(),
        "raw",
        "name_map_rows",
        &LIBRARY.replace("table: (b)", "r#table: (b)"),
    );
    let keyword = package(
        temporary.path(),
        "keyword",
        "name_map_rows",
        &LIBRARY.replace("table: (b)", "r#match: (b)"),
    );
    let plain_k = emitted_k(
        target.path(),
        &plain,
        "name_map_rows",
        &temporary.path().join("plain-out"),
    );
    assert_eq!(
        emitted_k(
            target.path(),
            &raw,
            "name_map_rows",
            &temporary.path().join("raw-out")
        ),
        plain_k
    );
    let (success, _, stderr) = krs(target.path(), &keyword, "name_map_rows", "check", &[]);
    assert!(success, "{stderr}");
    let keyword_k = emitted_k(
        target.path(),
        &keyword,
        "name_map_rows",
        &temporary.path().join("keyword-out"),
    );
    assert_eq!(
        keyword_k,
        plain_k.replace(
            "[label(org_krs_name_map--table)]",
            "[label(org_krs_name_map--match)]"
        )
    );
}

/// `LIBRARY` with each `(from, to)` replaced and `extra` appended.
fn library(replacements: &[(&str, &str)], extra: &str) -> String {
    let mut source = LIBRARY.to_owned();
    for (from, to) in replacements {
        assert!(source.contains(from), "{from}");
        source = source.replacen(from, to, 1);
    }
    source + extra
}

/// The headline of `krs check`'s first error on a package of `library`, or `None` when the
/// package checks.
fn check_headline(target: &Path, root: &Path, directory: &str, library: &str) -> Option<String> {
    let name = format!("name_map_{}", directory.replace('-', "_"));
    let manifest = package(root, directory, &name, library);
    let (success, _, stderr) = krs(target, &manifest, &name, "check", &[]);
    (!success).then(|| {
        stderr
            .lines()
            .find(|line| line.starts_with("error"))
            .unwrap_or_else(|| panic!("no error:\n{stderr}"))
            .to_owned()
    })
}

/// A declared sort and a constructor of it, appended to `LIBRARY`.
fn sort(name: &str) -> String {
    format!(
        "\nk::sorts! {{\n    {name};\n}}\n\n#[k::constructors(sort = {name}, result = KResult)]\npub enum {name}Syntax {{\n    #[k::syntax(\"mark\")]\n    Mark(),\n}}\n"
    )
}

/// `LIBRARY` with a function `name`, which the rule `unwrap` reads in place of `PickF`.
fn function(name: &str) -> String {
    library(
        &[("acc: PickF(v)", &format!("acc: {name}(v)"))],
        &format!(
            "\n#[k::function(total, internal)]\npub fn {name}(b: Term<Int>) -> Term<Int> {{\n    int::add(b, 2)\n}}\n"
        ),
    )
}

/// A name K already gives a meaning is one thing in K, so an authored declaration that takes it
/// would add to K's thing instead of declaring its own: K's own sorts, the sorts K generates for
/// the definition's cells, a symbol of a builtin module the definition imports (the
/// conditional's `ite`; a configuration imports `MAP`), a cell K adds to every configuration,
/// and a terminal K reads as a sentence keyword (a function's name gives its terminal). Each is
/// refused at the declaration, naming both. A name of a module the definition does not import
/// (`bigEndianBytes` without bytes), a word K reads as a keyword only between sentences
/// (`requires`), a sort K does not declare (`KVariable`, whose K sort is `#KVariable`) and a
/// cell named by a keyword stay accepted.
#[test]
fn a_name_k_gives_a_meaning_is_refused_at_the_declaration() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let collision = "error[krs::analysis::symbol-name-collision]: ";
    let cases = [
        (
            "sort-kcell",
            library(&[], &sort("KCell")),
            Some(
                "sort `KCell` of ORG-KRS-NAME-MAP has the K name \"KCell\", which K generates as the sort of the cell `<k>`",
            ),
        ),
        (
            "sort-kbott",
            library(&[], &sort("KBott")),
            Some(
                "sort `KBott` of ORG-KRS-NAME-MAP has the K name \"KBott\", which K declares as a sort of its own",
            ),
        ),
        ("sort-kvariable", library(&[], &sort("KVariable")), None),
        (
            "cell-generated-top",
            library(
                &[
                    (
                        "pub acc: Int,",
                        "pub acc: Int,\n    #[k::cell(name = \"generatedTop\")]\n    pub top: Int,",
                    ),
                    ("acc: 0 }", "acc: 0, top: 0 }"),
                ],
                "",
            ),
            Some(
                "the cell `top` has the K name \"generatedTop\", which K adds as the top cell of every configuration",
            ),
        ),
        (
            "cell-rule",
            library(
                &[
                    (
                        "pub acc: Int,",
                        "pub acc: Int,\n    #[k::cell]\n    pub rule: Int,",
                    ),
                    ("acc: 0 }", "acc: 0, rule: 0 }"),
                ],
                "",
            ),
            None,
        ),
    ];
    let functions = [
        (
            "fn-ite",
            "Ite",
            Some(
                "production `Ite` of ORG-KRS-NAME-MAP has the K name \"ite\", which K's builtin module `K-EQUAL` provides as a symbol (it or a module it imports declares it)",
            ),
        ),
        (
            "fn-size-map",
            "SizeMap",
            Some(
                "production `SizeMap` of ORG-KRS-NAME-MAP has the K name \"sizeMap\", which K's builtin module `MAP` provides as a symbol (it or a module it imports declares it)",
            ),
        ),
        ("fn-big-endian-bytes", "BigEndianBytes", None),
        (
            "fn-rule",
            "Rule",
            Some(
                "production `Rule` of ORG-KRS-NAME-MAP has the K name \"rule\", which is a terminal K reads as a sentence keyword: K ends a sentence's text at a bare `rule`, so a rule or claim that applies the production would end there",
            ),
        ),
        ("fn-requires", "Requires", None),
    ];
    let cases = cases
        .into_iter()
        .chain(functions.map(|(directory, name, expected)| (directory, function(name), expected)));
    for (directory, source, expected) in cases {
        assert_eq!(
            check_headline(target.path(), temporary.path(), directory, &source),
            expected.map(|reason| format!("{collision}{reason}")),
            "{directory}"
        );
    }
}

/// K spells a context alias's name without `_` (`before_any` is `beforeAny`), and aliases of one
/// K name are one evaluation strategy, so two aliases whose names differ only there are refused,
/// naming both, where K would join them.
#[test]
fn context_alias_names_k_spells_alike_are_refused() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let alias = |name: &str, function: &str| {
        format!(
            "\n#[k::context_alias(name = {name}, here = site)]\nfn {function}(\n    k::cells! {{ k: k::configuration::KCell(site, _, tail @ ..), state @ .. }}: Machine,\n) {{\n}}\n"
        )
    };
    let alike = library(
        &[],
        &(alias("before_any", "before_any") + &alias("beforeAny", "before_any2")),
    );
    assert_eq!(
        check_headline(target.path(), temporary.path(), "alias-alike", &alike).as_deref(),
        Some(
            "error[krs::analysis::name-collision]: emitted label name collision for \"beforeAny\" between context alias `before_any` and context alias `beforeAny`"
        )
    );
    let distinct = library(
        &[],
        &(alias("before_any", "before_any") + &alias("before_all", "before_all")),
    );
    assert_eq!(
        check_headline(target.path(), temporary.path(), "alias-distinct", &distinct),
        None
    );
}

/// A `k::rules!` clause's name is the rule's identifier, as a row's or a rule fn's is, not label
/// text: it gives the label its spelling with `_` written `-` where a K label spells that, and
/// otherwise the rule takes the hash label of its identity, as a row of that name does. A clause
/// whose name is spellable keeps its label.
#[test]
fn a_clause_name_no_k_label_spells_takes_the_hash_label() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let source = library(&[("unwrap: {", "dérouler: {")], "");
    assert_eq!(
        check_headline(target.path(), temporary.path(), "clause-name", &source),
        None
    );
    let manifest = temporary.path().join("clause-name/Cargo.toml");
    let emitted = emitted_k(
        target.path(),
        &manifest,
        "name_map_clause_name",
        &temporary.path().join("clause-out"),
    );
    let label = emitted
        .lines()
        .find_map(|line| line.trim().strip_prefix("rule [krsRule_"))
        .unwrap_or_else(|| panic!("no hash label:\n{emitted}"));
    assert!(label.ends_with("]:"), "{label}");
    let plain = package(temporary.path(), "plain", "name_map_plain", LIBRARY);
    let plain_k = emitted_k(
        target.path(),
        &plain,
        "name_map_plain",
        &temporary.path().join("plain-out"),
    );
    assert!(plain_k.contains("rule [unwrap]:"), "{plain_k}");
}

/// A raw identifier is the identifier itself, so an item declared raw is the item of its
/// identifier: a variant `r#Wrap` the rule writes `Wrap`, a function `r#PickF`, a sort `r#Stmt`,
/// a configuration `r#Machine` and a struct constructor `r#Inc` give the K of their plain twins
/// (the configuration's `// KRS` line names `Machine`).
#[test]
fn a_raw_item_is_the_item_of_its_identifier() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let inc = "\n#[k::constructor(sort = Stmt, syntax = \"inc({n})\")]\npub struct {name} {\n    pub n: Term<Int>,\n}\n";
    let twins = [
        (
            "variant",
            library(&[("Wrap { s: Stmt },", "r#Wrap { s: Stmt },")], ""),
            library(&[], ""),
        ),
        (
            "function",
            library(&[("pub fn PickF(", "pub fn r#PickF(")], ""),
            library(&[], ""),
        ),
        (
            "sort",
            library(
                &[("k::sorts! {\n    Stmt;", "k::sorts! {\n    r#Stmt;")],
                "",
            ),
            library(&[], ""),
        ),
        (
            "configuration",
            library(
                &[
                    ("pub struct Machine", "pub struct r#Machine"),
                    ("impl Machine", "impl r#Machine"),
                ],
                "",
            ),
            library(&[], ""),
        ),
        (
            "struct",
            library(&[], &inc.replace("{name}", "r#Inc")),
            library(&[], &inc.replace("{name}", "Inc")),
        ),
    ];
    for (directory, raw, plain) in twins {
        let raw_name = format!("name_map_raw_{directory}");
        let plain_name = format!("name_map_plain_{directory}");
        let raw_manifest = package(
            temporary.path(),
            &format!("raw-{directory}"),
            &raw_name,
            &raw,
        );
        let plain_manifest = package(
            temporary.path(),
            &format!("plain-{directory}"),
            &plain_name,
            &plain,
        );
        let (success, _, stderr) = krs(target.path(), &raw_manifest, &raw_name, "check", &[]);
        assert!(success, "{directory}: {stderr}");
        assert_eq!(
            emitted_k(
                target.path(),
                &raw_manifest,
                &raw_name,
                &temporary.path().join(format!("raw-{directory}-out"))
            ),
            emitted_k(
                target.path(),
                &plain_manifest,
                &plain_name,
                &temporary.path().join(format!("plain-{directory}-out"))
            ),
            "{directory}"
        );
    }
    let configuration =
        fs::read_to_string(temporary.path().join("raw-configuration-out/definition.k")).unwrap();
    assert!(
        configuration.contains("src/lib.rs: Machine\n"),
        "{configuration}"
    );
}

/// A raw keyword is named by its identifier, which has no plain spelling: a variant `r#match` has
/// the symbol `stmtSyntaxmatch`, and a field `r#type` is the cell `<type>`.
#[test]
fn a_raw_keyword_item_is_named_by_its_identifier() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    for (directory, source, spelled) in [
        (
            "variant-keyword",
            library(
                &[
                    ("Wrap { s: Stmt },", "r#match { s: Stmt },"),
                    ("Wrap { s }, ..", "r#match { s }, .."),
                ],
                "",
            ),
            "symbol(stmtSyntaxmatch)",
        ),
        (
            "cell-keyword",
            library(
                &[
                    ("pub acc: Int,", "pub r#type: Int,"),
                    ("acc: 0 }", "r#type: 0 }"),
                    (
                        "acc: v } => { k: [s, ..], acc: PickF(v) }",
                        "r#type: v } => { k: [s, ..], r#type: PickF(v) }",
                    ),
                ],
                "",
            ),
            "<type> V:Int => pickF ( V:Int ) </type>",
        ),
    ] {
        let name = format!("name_map_raw_{}", directory.replace('-', "_"));
        let manifest = package(temporary.path(), directory, &name, &source);
        let (success, _, stderr) = krs(target.path(), &manifest, &name, "check", &[]);
        assert!(success, "{directory}: {stderr}");
        let emitted = emitted_k(
            target.path(),
            &manifest,
            &name,
            &temporary.path().join(format!("{directory}-out")),
        );
        assert!(emitted.contains(spelled), "{directory}: {emitted}");
    }
}

/// A cell `<k>`, its sort `KCell` and a function's symbol `k` are names of K's three namespaces,
/// so a function `K` beside the cell `k` is its own name, and the rule applies it.
#[test]
fn a_function_k_beside_the_cell_k_is_another_name() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let manifest = package(
        temporary.path(),
        "function-k",
        "name_map_function_k",
        &function("K"),
    );
    let (success, _, stderr) = krs(
        target.path(),
        &manifest,
        "name_map_function_k",
        "check",
        &[],
    );
    assert!(success, "{stderr}");
    let emitted = emitted_k(
        target.path(),
        &manifest,
        "name_map_function_k",
        &temporary.path().join("function-k-out"),
    );
    assert!(
        emitted.contains("syntax Int ::= \"k\" \"(\" Int \")\" [symbol(k), function, total]")
            && emitted.contains("<acc> V:Int => k ( V:Int ) </acc>"),
        "{emitted}"
    );
}

/// A function's name must be ASCII `UpperCamelCase`, since its symbol is the name with a lowercase
/// first letter. A name with no such spelling (`Café`) is told why, not advised its own name; one
/// that has one (`Pick_f`) is advised it.
#[test]
fn a_function_name_with_no_ascii_spelling_is_told_why() {
    let target = shared_fixture_target();
    let temporary = temp_dir();
    let shorthand = "error[krs::syntax::invalid-function-shorthand]: a function symbol is named as its applications are written, ";
    for (directory, name, reason) in [
        (
            "fn-cafe",
            "Café",
            "in ASCII UpperCamelCase: its K symbol is the name with a lowercase first letter, which KRS spells with ASCII letters and digits only, and `Café` holds another character",
        ),
        (
            "fn-pick-f",
            "Pick_f",
            "in UpperCamelCase (`fn PickF`); its equation takes the snake_case name",
        ),
    ] {
        assert_eq!(
            check_headline(target.path(), temporary.path(), directory, &function(name)),
            Some(format!("{shorthand}{reason}")),
            "{directory}"
        );
    }
}

/// One prelude module: its imports, the sorts it declares and the symbols of its productions.
#[derive(Default)]
struct PreludeModule {
    imports: Vec<String>,
    sorts: std::collections::BTreeSet<String>,
    symbols: std::collections::BTreeSet<String>,
}

/// The modules of the prelude the emitted K is loaded with: k-rust's bundled `kast.md` and
/// `domains.md`, read by k-rust's own parser.
fn prelude() -> std::collections::BTreeMap<String, PreludeModule> {
    let mut modules = std::collections::BTreeMap::new();
    for file in ["kast.md", "domains.md"] {
        let source = k_rust::builtin::embedded(file).expect("k-rust bundles the file");
        let code = k_rust::outer::extract_fenced_k_code(&source.text, "k").unwrap();
        let parsed = k_rust::outer::parse(source.source.clone(), &code).unwrap();
        for module in parsed.modules {
            let mut read = PreludeModule {
                imports: module
                    .imports
                    .iter()
                    .map(|import| import.module.clone())
                    .collect(),
                ..PreludeModule::default()
            };
            for sentence in &module.sentences {
                let k_rust::outer::Sentence::Syntax(declaration) = sentence else {
                    continue;
                };
                // A sort parameter (`syntax {Sort} Sort ::= ..`) is no sort of the module.
                if !declaration
                    .parameters
                    .iter()
                    .any(|parameter| parameter.name == declaration.sort.name)
                {
                    read.sorts.insert(declaration.sort.name.clone());
                }
                if let k_rust::outer::SyntaxBody::Productions(blocks) = &declaration.body {
                    for production in blocks.iter().flat_map(|block| &block.productions) {
                        read.symbols.extend(
                            production
                                .attributes
                                .iter()
                                .filter(|attribute| attribute.key == "symbol")
                                .filter_map(|attribute| attribute.value.clone()),
                        );
                    }
                }
            }
            modules.insert(module.name, read);
        }
    }
    modules
}

/// `module` and every module it imports, directly or through others.
fn closure<'a>(
    modules: &'a std::collections::BTreeMap<String, PreludeModule>,
    module: &str,
) -> Vec<&'a PreludeModule> {
    let mut seen = std::collections::BTreeSet::new();
    let mut pending = vec![module.to_owned()];
    let mut closure = Vec::new();
    while let Some(name) = pending.pop() {
        if let Some(read) = modules.get(&name)
            && seen.insert(name)
        {
            pending.extend(read.imports.iter().cloned());
            closure.push(read);
        }
    }
    closure
}

/// KRS's tables of the names K gives a meaning (`krs-compiler` `k_reserved`) are the names of the
/// prelude the emitted K is loaded with, k-rust's bundled `kast.md` and `domains.md`: every entry
/// is a sort or symbol its module declares (it or a module it imports), brought in by each
/// module it lists, and K's own sorts are those of `K` and its cell modules. With
/// [`the_bundled_prelude_s_names_are_reserved`], a prelude update fails here instead of leaving
/// the tables behind.
#[test]
fn the_reserved_names_are_in_the_bundled_prelude() {
    let mut failures = Vec::new();
    macro_rules! expect {
        ($holds:expr, $($message:tt)*) => {
            if !$holds {
                failures.push(format!($($message)*));
            }
        };
    }
    let modules = prelude();
    let (kast_sorts, symbols, module_sorts) = krs_compiler::testing::reserved_k_names();
    let declares = |module: &str, sort: bool, name: &str| {
        closure(&modules, module).into_iter().any(|read| {
            if sort {
                read.sorts.contains(name)
            } else {
                read.symbols.contains(name)
            }
        })
    };
    let brings = |importer: &str, module: &str| {
        closure(&modules, importer)
            .into_iter()
            .any(|read| std::ptr::eq(read, std::ptr::from_ref(&modules[module])))
    };
    // A definition imports K's own modules: with a configuration, `MAP`; without one, K's
    // default configuration.
    let every = ["MAP", "DEFAULT-CONFIGURATION"];
    for (tables, sort) in [(symbols, false), (module_sorts, true)] {
        for (name, module, importers) in tables {
            expect!(declares(module, sort, name), "{module} declares {name}");
            let importers = if importers.is_empty() {
                &every[..]
            } else {
                importers
            };
            for importer in importers {
                expect!(brings(importer, module), "{importer} brings {module}");
            }
        }
    }
    // K's own modules: `K`, and the cell syntax every rule and configuration is parsed with.
    let own = ["K", "RULE-CELLS", "CONFIG-CELLS"];
    let k_sorts = own
        .into_iter()
        .flat_map(|module| closure(&modules, module))
        .flat_map(|read| read.sorts.iter().cloned())
        .collect::<std::collections::BTreeSet<_>>();
    for sort in kast_sorts {
        expect!(k_sorts.contains(*sort), "K declares {sort}");
    }

    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The other way: every sort and symbol an author can spell (a sort is ASCII, starting uppercase;
/// a symbol starts lowercase or with `_`) of a prelude module a definition can import is in a
/// table, or is a builtin sort of KRS, the framework's, or a cell sort K generates.
#[test]
fn the_bundled_prelude_s_names_are_reserved() {
    let mut failures = Vec::new();
    macro_rules! expect {
        ($holds:expr, $($message:tt)*) => {
            if !$holds {
                failures.push(format!($($message)*));
            }
        };
    }
    let modules = prelude();
    let (kast_sorts, symbols, module_sorts) = krs_compiler::testing::reserved_k_names();
    let every = ["MAP", "DEFAULT-CONFIGURATION"];
    let own = ["K", "RULE-CELLS", "CONFIG-CELLS"];
    let spellable_sort = |sort: &str| {
        sort.starts_with(|first: char| first.is_ascii_uppercase())
            && sort.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    };
    let spellable_symbol = |symbol: &str| {
        symbol.starts_with(|first: char| first.is_ascii_lowercase() || first == '_')
            && symbol
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_')
    };
    let builtin = krs_ir::BuiltinSort::ALL
        .iter()
        .map(|sort| sort.k_name())
        .chain([
            "KItem",
            "KResult",
            "GeneratedCounterCell",
            "GeneratedTopCell",
        ])
        .collect::<std::collections::BTreeSet<_>>();
    // The modules a definition can import: each builtin sort's and operation's, K's
    // matching-logic and symbolic-map modules and the one declaring `K`, the collections
    // module, unsigned integer syntax, and K's own.
    let mut importable = krs_ir::BuiltinSort::ALL
        .iter()
        .flat_map(|sort| [sort.spec().k_module, sort.spec().k_syntax_module])
        .flatten()
        .chain(
            krs_ir::BuiltinOperation::ALL
                .iter()
                .map(|operation| operation.spec().k_module),
        )
        .chain([
            krs_ir_levels::k_surface::ML_SYNTAX_MODULE,
            krs_ir_levels::k_surface::MAP_SYMBOLIC_MODULE,
            krs_ir_levels::k_surface::SORT_K_MODULE,
            "COLLECTIONS",
            "UNSIGNED-INT-SYNTAX",
        ])
        .chain(every)
        .collect::<std::collections::BTreeSet<_>>();
    importable.extend(own);
    for module in importable {
        expect!(
            modules.contains_key(module),
            "the prelude declares {module}"
        );
        let reach = closure(&modules, module);
        for symbol in reach
            .iter()
            .flat_map(|read| &read.symbols)
            .filter(|symbol| spellable_symbol(symbol))
        {
            expect!(
                symbols.iter().any(|(name, _, importers)| *name == symbol
                    && (importers.is_empty() || importers.contains(&module))),
                "{module} brings the symbol {symbol}, which no table entry reserves there"
            );
        }
        for sort in reach
            .iter()
            .flat_map(|read| &read.sorts)
            .filter(|sort| spellable_sort(sort))
        {
            expect!(
                builtin.contains(sort.as_str())
                    || kast_sorts.contains(&sort.as_str())
                    || module_sorts
                        .iter()
                        .any(|(name, _, importers)| *name == sort && importers.contains(&module)),
                "{module} brings the sort {sort}, which no table entry reserves there"
            );
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
