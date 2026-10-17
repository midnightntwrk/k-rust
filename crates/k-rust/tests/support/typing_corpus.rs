// The corpus of compiled definitions the typing-view property tests run over, shared by
// `tests/sentence_typing.rs` and the crate's own test of the computation-cell decision
// (`kompile::passes::add_implicit_computation_cell`), which include this file.

/// The definitions of the corpus property: the single-module reference fixtures, the
/// sentence-typing fixtures, and copies of K regression definitions (`pyk/regression-new`, files
/// kept byte for byte) whose rules use local functions, `:=K`, field projections, `#withConfig`
/// and a module that lacks `K`. K's withConfig2 is not among them: krust refuses its
/// fresh-variable function rule, and its own test types its `#withConfig` rule.
fn corpus() -> Vec<(String, String, String, Option<std::path::PathBuf>)> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut corpus = Vec::new();
    let reference = root.join("reference");
    let mut files = std::fs::read_dir(&reference)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "k"))
        .collect::<Vec<_>>();
    files.sort();
    for path in files {
        let text = std::fs::read_to_string(&path).unwrap();
        let main = text
            .lines()
            .rev()
            .find_map(|line| line.trim_start().strip_prefix("module "))
            .unwrap()
            .trim()
            .to_owned();
        corpus.push((
            path.file_name().unwrap().to_string_lossy().into_owned(),
            text,
            main,
            Some(reference.clone()),
        ));
    }
    for (file, main) in [
        ("regression/equals-pattern.k", "TEST"),
        ("regression/let-test.k", "TEST"),
        ("regression/total-proj.k", "TEST"),
        ("regression/issue-2114.k", "TEST"),
        ("generated-rule-syntax.k", "TYPER-PROBE"),
        ("private-helpers.k", "PRIV"),
        ("inferred-parent.k", "INFERRED-PARENT"),
        ("regression/withConfig.k", "TEST"),
        ("configuration-context.k", "TYPER-CFG"),
        ("transaction-data.k", "TX-DATA"),
        ("collection-cell-content.k", "TEST"),
        ("private-configuration-context.k", "P"),
        ("cell-less-bound.k", "CELL-LESS-BOUND"),
        ("generated-heads.k", "GENERATED-HEADS"),
    ] {
        let path = root.join("sentence-typing").join(file);
        corpus.push((
            file.to_owned(),
            std::fs::read_to_string(&path).unwrap(),
            main.to_owned(),
            None,
        ));
    }
    corpus
}
