//! The public claim-free mutant accessor (kink-campaign `claim_free_mutant`, ticket KINK-MUTSIDE,
//! fz26 P7-KINKFLOW T2): for every mutation of `examples/imp`, of the `first-zero` flow (an
//! equation edit whose `total` claim the mutant loses) and of the `overlap` fixture (an
//! inconsistent mutant), the accessor gives exactly what the runner's mutant preparation gives.
//! A mutant the accessor builds is the claim-free mutant (its compiled KORE is that of the patch,
//! or of the withdrawing patch when the edit leaves claims unbacked) and the runner gives it no
//! mutant-scope failure; a refusal carries the run row's reason and inconsistent pairs.

mod flow_support;

use flow_support::{copy_dir, corpus_run, flow};
use kink_campaign::{MutantAdmission, MutantStage, claim_free_mutant};
use kink_corpus::cli::DEFINITION_STACK_BYTES;
use kink_flow::{FlowManifest, MutationList, admit::admit, resolve};
use kink_patch::ClaimSupport;
use serde_json::{Value, json};
use std::{
    fs,
    path::{Path, PathBuf},
};

fn scratch(name: &str) -> PathBuf {
    let dir = Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("kink-flow-claim-free-{}", std::process::id()))
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// The reason a run row gives for a mutant-scope failure (kink-flow `search`'s kebab case of the
/// failure's name).
fn reason(failure: kink_campaign::MutantScopeFailure) -> String {
    let mut out = String::new();
    for (index, character) in format!("{failure:?}").chars().enumerate() {
        if character.is_uppercase() {
            if index > 0 {
                out.push('-');
            }
            out.extend(character.to_lowercase());
        } else {
            out.push(character);
        }
    }
    out
}

/// Checks every mutation of the flow in `dir` against its row of a cold `kink-flow run`, and
/// returns how many mutants the accessor built and how many it refused.
fn agrees_with_the_runner(dir: &Path) -> (usize, usize) {
    let (document, _) = corpus_run(&dir.join("FLOW.toml"), &dir.join("MUTATIONS.toml"));
    let manifest = FlowManifest::read(&dir.join("FLOW.toml")).unwrap();
    let list = MutationList::read(&dir.join("MUTATIONS.toml")).unwrap();
    let admission = admit(&manifest);
    let spec = admission.spec.expect("the specification is admitted");
    let baseline = spec.validator.baseline();
    let mutant_admission = MutantAdmission::new(
        baseline,
        &spec.compiled,
        &k_rust::kast::identifier::encode(&manifest.spec.main_module),
        &[],
    );
    let support = ClaimSupport::new(baseline);
    let (mut built, mut refused) = (0, 0);
    for mutation in &list.mutations {
        let row = document["mutations"]
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["id"] == mutation.id.as_str())
            .unwrap_or_else(|| panic!("no row {}", mutation.id));
        let Ok(resolved) = resolve(&manifest, &spec.loaded, mutation) else {
            assert_eq!(row["status"], "invalid-mutation", "{}", mutation.id);
            continue;
        };
        let mut stages = Vec::new();
        match claim_free_mutant(
            &spec.validator,
            &spec.compiled,
            &resolved.patch,
            &mutant_admission,
            &mut |stage| stages.push(stage),
        ) {
            Ok(mutant) => {
                built += 1;
                assert_eq!(
                    stages,
                    [MutantStage::Backend, MutantStage::Consistency],
                    "{}",
                    mutation.id
                );
                let claims = support.withdraw(baseline, &resolved.patch).unwrap();
                assert_eq!(mutant.claims, claims, "{}", mutation.id);
                let claim_free = claims.patch().unwrap_or(&resolved.patch);
                let compiled = spec.validator.validate(claim_free).unwrap();
                assert_eq!(
                    mutant.side.kore_sha256(),
                    compiled.kore_sha256(),
                    "{}: the accessor's mutant is the claim-free compile",
                    mutation.id
                );
                assert!(
                    ["killed", "survived", "unknown", "timeout"]
                        .contains(&row["status"].as_str().unwrap()),
                    "{}: {row:#}",
                    mutation.id
                );
                assert_eq!(row["inconsistent_pairs"], json!([]), "{}", mutation.id);
            }
            Err(refusal) => {
                refused += 1;
                assert_eq!(
                    row["reason"],
                    reason(refusal.failure),
                    "{}: {row:#}",
                    mutation.id
                );
                let pairs = refusal
                    .inconsistent_pairs
                    .iter()
                    .map(kink_native::consistency::UnjoinedEquations::value)
                    .collect::<Vec<_>>();
                assert_eq!(
                    row["inconsistent_pairs"],
                    Value::Array(pairs),
                    "{}",
                    mutation.id
                );
            }
        }
    }
    (built, refused)
}

fn on_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(DEFINITION_STACK_BYTES)
        .spawn(body)
        .unwrap()
        .join()
        .unwrap();
}

mod kink_tier {
    use super::*;

    #[test]
    #[ignore = "kink"]
    fn every_imp_mutation_is_prepared_as_the_runner_prepares_it() {
        on_stack(|| {
            let dir = scratch("imp").join("imp");
            copy_dir(
                &Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/imp"),
                &dir,
            );
            // Every IMP mutation compiles, is consistent and runs.
            assert_eq!(agrees_with_the_runner(&dir), (21, 0));
        });
    }

    #[test]
    #[ignore = "kink"]
    fn an_equation_edit_loses_its_claim_as_in_the_runner() {
        on_stack(|| {
            let dir = scratch("first-zero");
            fs::write(
                dir.join("modview.k"),
                "module MODVIEW-SYNTAX\n  imports INT-SYNTAX\n  syntax Pgm ::= go(Int)\nendmodule\n\n\
                 module TWICE\n  imports INT-SYNTAX\n  syntax KItem ::= step(Int) | done(Int)\n  \
                 syntax K ::= first(Int) [function, total]\n  \
                 rule [twice]: step(X) => done(X) ~> done(X)\n  rule [first]: first(X) => done(X)\n\
                 endmodule\n\n\
                 module MODVIEW\n  imports MODVIEW-SYNTAX\n  imports TWICE\n  imports INT\n  \
                 configuration <k> $PGM:Pgm </k>\n  rule [go]: go(X) => step(X) ~> first(X)\nendmodule\n",
            )
            .unwrap();
            fs::write(
                dir.join("FLOW.toml"),
                "[spec]\nentry = \"modview.k\"\nmain_module = \"MODVIEW\"\nsyntax_module = \"MODVIEW-SYNTAX\"\n\n\
                 [[program]]\nid = \"one\"\ntext = \"go(1)\"\n",
            )
            .unwrap();
            fs::write(
                dir.join("MUTATIONS.toml"),
                "[[mutation]]\nid = \"first-zero\"\n\n  [[mutation.edit]]\n  rule = \"first\"\n  \
                 find = \"done(X)\"\n  replace = \"done(0)\"\n",
            )
            .unwrap();
            assert_eq!(agrees_with_the_runner(&dir), (1, 0));
        });
    }

    #[test]
    #[ignore = "kink"]
    fn an_inconsistent_mutant_is_refused_with_the_rows_pairs() {
        on_stack(|| {
            let dir = scratch("overlap").join("overlap");
            copy_dir(&flow("overlap"), &dir);
            assert_eq!(agrees_with_the_runner(&dir), (1, 1));
        });
    }
}
