use std::{
    fs,
    path::{Path, PathBuf},
};

use k_rust::kompile::CompileOptions;
use kink_corpus::{CorpusSource, LoadError, load_source};
use kink_native::NativeValidator;
use kink_patch::{SemanticInput, sha256};

fn fixture() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../testdata/corpus/relative")
}

fn copy_fixture(label: &str) -> PathBuf {
    let root =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("cs02-{label}-{}", std::process::id()));
    fs::create_dir_all(root.join("definition")).unwrap();
    fs::create_dir_all(root.join("include")).unwrap();
    for name in ["definition/main.k", "include/syntax.k"] {
        fs::copy(fixture().join(name), root.join(name)).unwrap();
    }
    root
}

fn source(root: &Path) -> CorpusSource {
    CorpusSource {
        root: root.to_owned(),
        entry: "definition/main.k".into(),
        include_dirs: vec!["include".into()],
        main_module: "CORPUS".into(),
        syntax_module: Some("CORPUS-SYNTAX".into()),
        md_selector: None,
    }
}

#[test]
fn relocation_is_invisible() {
    let a = copy_fixture("relocate-a");
    let b = copy_fixture("relocate-b");
    let left = load_source(&source(&a)).unwrap();
    let right = load_source(&source(&b)).unwrap();
    let left_input = SemanticInput::of(&left.baseline).unwrap();
    let right_input = SemanticInput::of(&right.baseline).unwrap();
    assert_eq!(left_input.digest(), right_input.digest());
    assert_eq!(left_input.text(), right_input.text());
    assert_eq!(
        SemanticInput::read(left_input.text()).unwrap().0,
        left_input
    );
    assert_eq!(left.files, right.files);
    assert_eq!(
        left.files
            .iter()
            .map(|file| file.name.as_str())
            .collect::<Vec<_>>(),
        ["definition/main.k", "include/syntax.k"]
    );
    for file in &left.files {
        assert_eq!(file.sha256, sha256(&fs::read(a.join(&file.name)).unwrap()));
        assert!(!Path::new(&file.name).is_absolute());
    }
    let left_compiled = NativeValidator::bind(left.baseline, CompileOptions::default())
        .compile_baseline()
        .unwrap();
    let right_compiled = NativeValidator::bind(right.baseline, CompileOptions::default())
        .compile_baseline()
        .unwrap();
    assert_eq!(left_compiled.kore_sha256(), right_compiled.kore_sha256());
    for root in [&a, &b] {
        let path = root.to_str().unwrap();
        assert!(!left_input.text().contains(path));
        assert!(!right_input.text().contains(path));
        assert!(!left_compiled.artifacts().definition_kore.contains(path));
        assert!(!right_compiled.artifacts().definition_kore.contains(path));
        assert!(left.files.iter().all(|file| !file.name.contains(path)));
    }
    fs::remove_dir_all(a).unwrap();
    fs::remove_dir_all(b).unwrap();
}

#[test]
fn lookup_order() {
    let root = copy_fixture("lookup");
    fs::copy(
        root.join("include/syntax.k"),
        root.join("definition/syntax.k"),
    )
    .unwrap();
    let loaded = load_source(&source(&root)).unwrap();
    assert!(
        loaded
            .files
            .iter()
            .any(|file| file.name == "include/syntax.k")
    );
    assert!(
        !loaded
            .files
            .iter()
            .any(|file| file.name == "definition/syntax.k")
    );
    fs::remove_file(root.join("include/syntax.k")).unwrap();
    fs::create_dir_all(root.join("later")).unwrap();
    fs::copy(
        root.join("definition/syntax.k"),
        root.join("later/syntax.k"),
    )
    .unwrap();
    let mut spec = source(&root);
    spec.include_dirs.push("later".into());
    let loaded = load_source(&spec).unwrap();
    assert!(
        loaded
            .files
            .iter()
            .any(|file| file.name == "definition/syntax.k")
    );
    assert!(
        !loaded
            .files
            .iter()
            .any(|file| file.name == "later/syntax.k")
    );
    fs::remove_file(root.join("definition/syntax.k")).unwrap();
    let loaded = load_source(&spec).unwrap();
    assert!(
        loaded
            .files
            .iter()
            .any(|file| file.name == "later/syntax.k")
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn nested_require_falls_back_from_a_missing_root_include_candidate() {
    let root = copy_fixture("nested-require");
    let entry = fs::read_to_string(root.join("definition/main.k")).unwrap();
    fs::write(
        root.join("definition/main.k"),
        entry.replace("requires \"syntax.k\"", "requires \"../include/syntax.k\""),
    )
    .unwrap();
    let mut spec = source(&root);
    spec.include_dirs = vec![String::new()];
    let loaded = load_source(&spec).unwrap();
    assert_eq!(
        loaded
            .files
            .iter()
            .map(|file| file.name.as_str())
            .collect::<Vec<_>>(),
        ["definition/main.k", "include/syntax.k"],
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn escape_is_refused() {
    let root = copy_fixture("escape");
    let mut spec = source(&root);
    spec.entry = "../x.k".into();
    assert!(matches!(load_source(&spec), Err(LoadError::OutsideRoot)));
    spec.entry = fixture().join("definition/main.k").to_str().unwrap().into();
    assert!(matches!(load_source(&spec), Err(LoadError::OutsideRoot)));
    spec = source(&root);
    fs::write(
        root.join("definition/main.k"),
        "requires \"../../x.k\"\nmodule CORPUS endmodule\n",
    )
    .unwrap();
    assert!(matches!(load_source(&spec), Err(LoadError::OutsideRoot)));
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn symlink_escape_is_refused() {
    let root = copy_fixture("symlink");
    fs::remove_file(root.join("include/syntax.k")).unwrap();
    std::os::unix::fs::symlink(
        fs::canonicalize(fixture().join("include/syntax.k")).unwrap(),
        root.join("include/syntax.k"),
    )
    .unwrap();
    assert!(matches!(
        load_source(&source(&root)),
        Err(LoadError::OutsideRoot)
    ));
    let mut spec = source(&root);
    spec.entry = "include/syntax.k".into();
    assert!(matches!(load_source(&spec), Err(LoadError::OutsideRoot)));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn embedded_precedes_requiring_directory_without_includes() {
    let root = copy_fixture("builtin-order");
    let entry = fs::read_to_string(root.join("definition/main.k")).unwrap();
    fs::write(
        root.join("definition/main.k"),
        format!("requires \"domains.md\"\n{entry}"),
    )
    .unwrap();
    fs::write(root.join("definition/domains.md"), "invalid shadow builtin").unwrap();
    fs::copy(
        root.join("include/syntax.k"),
        root.join("definition/syntax.k"),
    )
    .unwrap();
    let mut spec = source(&root);
    spec.include_dirs.clear();
    let loaded = load_source(&spec).unwrap();
    assert!(
        !loaded
            .files
            .iter()
            .any(|file| file.name == "definition/domains.md")
    );
    assert!(
        loaded
            .files
            .iter()
            .any(|file| file.name == "definition/syntax.k")
    );
    fs::remove_dir_all(root).unwrap();
}
