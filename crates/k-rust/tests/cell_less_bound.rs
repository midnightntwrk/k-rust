//! A rule's rewrite whose sides have several minimal common supersorts.
//!
//! The parsed rewrite node carries a sort instance, but the loaded `Term::Rewrite` has none, and
//! compilation places each side of a rule's rewrite at the sort of the position it fills: a
//! cell-less rule is wrapped in the computation cell, where each side is an item of the `<k>`
//! sequence, as it is in a rule or claim written in that cell, and a side at an argument is
//! placed at the argument's sort. So no least upper bound of the two sides is needed to compile
//! such a rule, and both builds accept `rule a(X) => b(X)` in a module where `A` and `B` have the
//! two common supersorts `C` and `D`, compiling it to the rewrite axiom of the module where they
//! have one. A cell-less claim is not wrapped: compilation places it at the join of its sides, so
//! it still needs a unique bound, which injection requires. Every other parametric production
//! keeps the rule that its bounded parameters have a unique least upper bound, since its instance
//! is the sort of a term the compiled definition holds.
//!
//! The axiom snapshots are shared by both builds, so each build compiles each rule to the same
//! rewrite axiom.

use k_rust::builtin;
use k_rust::kompile::{CompilationBackend, CompileOptions, compile_loaded_definition};
use k_rust::outer::{LoadOptions, ResolvedSource, load_for_compilation};

/// The two-supersort definition, with `{rule}` its rewrite rule and `{lattice}` the supersorts
/// of `A` and `B` it declares.
fn source(module: &str, lattice: &str, rule: &str) -> String {
    format!(
        "module {module}-SYNTAX
  imports INT-SYNTAX
  syntax Pgm ::= go(Int) [symbol(go)]
endmodule

module {module}
  imports {module}-SYNTAX
  imports INT
  syntax A ::= a(Int) [symbol(a)]
  syntax B ::= b(Int) [symbol(b)]
{lattice}
  configuration <k> $PGM:Pgm </k>
  rule [go]: go(X) => a(X)
  {rule}
endmodule
"
    )
}

const TWO_SUPERSORTS: &str = "  syntax C ::= A | B\n  syntax D ::= A | B";

/// The lattices of `A` and `B`: two common supersorts, one of either, none.
const LATTICES: [(&str, &str); 4] = [
    ("CD", TWO_SUPERSORTS),
    ("C", "  syntax C ::= A | B"),
    ("D", "  syntax D ::= A | B"),
    ("none", ""),
];

/// The rewrite rules whose sides `a(X)` and `b(X)` have the lattice's common supersorts as their
/// bounds: cell-less, and written inside the computation cell with and without its frame.
const RULES: [(&str, &str); 3] = [
    ("cell-less", "rule [ab]: a(X) => b(X)"),
    ("in-cell", "rule [ab]: <k> a(X) => b(X) ... </k>"),
    ("whole-cell", "rule [ab]: <k> a(X) => b(X) </k>"),
];

fn compile(name: &str, source: &str, main: &str) -> Result<String, String> {
    let mut resolver =
        |_: &str, required: &str| builtin::embedded(required).ok_or_else(|| required.to_owned());
    let (loaded, _) = load_for_compilation(
        ResolvedSource::new(name, source.to_owned()),
        main,
        None,
        &mut resolver,
        &LoadOptions {
            implicit_sources: vec![builtin::embedded("prelude.md").unwrap()],
            excluded_module_attributes: vec![
                CompilationBackend::Rust
                    .excluded_module_attribute()
                    .to_owned(),
            ],
            ..LoadOptions::default()
        },
    )
    .map_err(|error| error.to_string())?;
    compile_loaded_definition(&loaded, CompileOptions::default())
        .map(|artifacts| artifacts.definition_kore)
        .map_err(|error| error.to_string())
}

/// The axiom labelled `label`, up to its `UNIQUE'Unds'ID` attribute, which hashes the module.
fn axiom<'a>(kore: &'a str, label: &str) -> &'a str {
    let needle = format!("label{{}}(\"{label}\")");
    let at = kore
        .find(&needle)
        .unwrap_or_else(|| panic!("no axiom {label}"));
    let start = kore[..at].rfind("axiom{").expect("an axiom");
    let axiom = &kore[start..at + needle.len()];
    axiom
        .find("UNIQUE'Unds'ID")
        .map_or(axiom, |end| &axiom[..end])
}

/// A rewrite at an argument position of a sort `E` above both common supersorts, where each side
/// is placed at `E`.
const ARGUMENT: (&str, &str) = (
    "argument",
    "syntax E ::= C | D\n  syntax F ::= e(E) [symbol(e)]\n  rule [ab]: <k> e(a(X) => b(X)) ... </k>",
);

/// Each rule's rewrite under two common supersorts compiles, in either build, to the same
/// rewrite axiom (the shared snapshot of `CL.ab`, up to its `UNIQUE'Unds'ID`).
#[test]
fn a_rewrite_under_two_common_supersorts_compiles_to_the_same_axiom_in_both_builds() {
    for (shape, rule) in RULES.into_iter().chain([ARGUMENT]) {
        let kore = compile("cl.k", &source("CL", TWO_SUPERSORTS, rule), "CL")
            .unwrap_or_else(|error| panic!("{shape}: the definition should compile: {error}"));
        insta::with_settings!({
            description => format!(
                "the CL.ab axiom of `{rule}` where A and B have the common supersorts C and D, rust backend, up to its UNIQUE'Unds'ID"
            ),
            omit_expression => true,
            prepend_module_to_snapshot => true,
            snapshot_suffix => shape,
        }, {
            insta::assert_snapshot!("two_supersort_rewrite_axiom", axiom(&kore, "CL.ab"));
        });
    }
}

/// The rewrite's sort instance does not reach the compiled rule: its axiom is the same under two
/// common supersorts, one of either, and none.
#[test]
fn the_rewrite_axiom_is_the_same_whatever_common_supersorts_its_sides_have() {
    for (shape, rule) in RULES {
        let axioms = LATTICES
            .iter()
            .map(|(lattice, declarations)| {
                let kore = compile("cl.k", &source("CL", declarations, rule), "CL").unwrap_or_else(
                    |error| {
                        panic!("{shape} under {lattice}: the definition should compile: {error}")
                    },
                );
                (*lattice, axiom(&kore, "CL.ab").to_owned())
            })
            .collect::<Vec<_>>();
        for (lattice, text) in &axioms[1..] {
            assert_eq!(
                &axioms[0].1, text,
                "{shape}: the ab axiom under {lattice} differs from the one under CD"
            );
        }
    }
}

/// A parametric production other than the rewrite still needs a unique least upper bound of its
/// bounds, in both builds: `pick(a(X), b(X))` with `{S} S ::= pick(S, S)`, and no rewrite under
/// it, would be a term of the compiled rule at the instance chosen, and `C` and `D` are two
/// minimal choices.
#[test]
fn a_parametric_production_other_than_the_rewrite_needs_a_unique_bound() {
    for (name, rule) in [
        ("right side", "rule [p]: go(X) => pick(a(X), b(X))"),
        (
            "in a cell",
            "rule [p]: <k> go(X) => pick(a(X), b(X)) ... </k>",
        ),
        ("left side", "rule [p]: pick(a(X), b(X)) => a(X)"),
    ] {
        let rule = format!("syntax {{S}} S ::= pick(S, S) [symbol(pick)]\n  {rule}");
        let error =
            compile("pick.k", &source("PICK", TWO_SUPERSORTS, &rule), "PICK").expect_err(name);
        assert!(
            error.contains(
                "could not parse rule in module \"PICK\": could not compute a unique least upper bound for parametric production bounds: A, B"
            ),
            "{name}: {error}"
        );
    }
}

#[cfg(feature = "cli")]
mod cli {
    use std::fs;
    use std::path::PathBuf;
    use std::process::{Command, Stdio};

    use super::{TWO_SUPERSORTS, compile, source};

    fn directory(name: &str) -> PathBuf {
        let directory = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("cell-less-bound-{}-{name}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir_all(&directory).unwrap();
        directory
    }

    /// `krust kcompile` writes the `definition.kore` the library compiles.
    #[test]
    fn krust_kcompile_compiles_the_two_supersort_rewrite_as_the_library_does() {
        let directory = directory("kcompile");
        let path = directory.join("cl.k");
        let text = source("CL", TWO_SUPERSORTS, "rule [ab]: a(X) => b(X)");
        fs::write(&path, &text).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args(["kcompile", "-m", "CL", "-o"])
            .arg(directory.join("out"))
            .arg(&path)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let written = fs::read_to_string(directory.join("out/definition.kore")).unwrap();
        let library = compile(path.to_str().unwrap(), &text, "CL").unwrap();
        assert!(written == library, "krust kcompile and the library differ");
        fs::remove_dir_all(directory).unwrap();
    }

    /// `krust kprove` parses a spec importing the module and proves the claim the two rules
    /// state.
    #[test]
    fn krust_kprove_proves_a_claim_over_the_two_supersort_rewrite() {
        let directory = directory("kprove");
        let path = directory.join("cl-spec.k");
        let text = format!(
            "{}\nmodule CL-SPEC\n  imports CL\n  claim <k> go(1) => b(1) </k>\nendmodule\n",
            source("CL", TWO_SUPERSORTS, "rule [ab]: a(X) => b(X)")
        );
        fs::write(&path, text).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                "--main-module",
                "CL-SPEC",
                "--definition-module",
                "CL",
            ])
            .arg(&path)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success()
                && stdout
                    .lines()
                    .any(|line| line.starts_with("claim #1: proven")),
            "{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        fs::remove_dir_all(directory).unwrap();
    }

    /// `krust kprove` of the one claim of a spec importing CL: its standard output and error.
    fn kprove(name: &str, claim: &str) -> (bool, String, String) {
        let directory = directory(name);
        let path = directory.join("cl-spec.k");
        let text = format!(
            "{}\nmodule CL-SPEC\n  imports CL\n  {claim}\nendmodule\n",
            source("CL", TWO_SUPERSORTS, "rule [ab]: a(X) => b(X)")
        );
        fs::write(&path, text).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_krust"))
            .args([
                "kprove",
                "--main-module",
                "CL-SPEC",
                "--definition-module",
                "CL",
            ])
            .arg(&path)
            .stdin(Stdio::null())
            .output()
            .unwrap();
        fs::remove_dir_all(directory).unwrap();
        (
            output.status.success(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    }

    /// A claim written in the computation cell places each side of its rewrite in the cell's
    /// sequence, so `<k> a(1) => b(1) </k>` needs no bound of `A` and `B` and is proven by the
    /// rule `ab`; a cell-less claim is compiled at the join of its sides, so `a(1) => b(1)`
    /// still needs a unique bound, and injection rejects it.
    #[test]
    fn a_claim_needs_a_bound_of_its_sides_only_outside_the_computation_cell() {
        let (success, stdout, stderr) = kprove("claim-in-cell", "claim <k> a(1) => b(1) </k>");
        assert!(
            success
                && stdout
                    .lines()
                    .any(|line| line.starts_with("claim #1: proven")),
            "{stdout}\n{stderr}"
        );
        let (success, stdout, stderr) = kprove("claim-cell-less", "claim a(1) => b(1)");
        assert!(!success, "{stdout}");
        assert!(
            stderr.contains("add sort injections")
                && stderr.contains("cannot compute a unique least upper bound for A, B"),
            "{stdout}\n{stderr}"
        );
    }
}
