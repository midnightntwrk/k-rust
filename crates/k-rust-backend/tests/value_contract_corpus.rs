//! The verdicts of the load-time critical-pair check on whole definitions (the value contract's
//! V12 gate, `scripts/value-contract-corpus.sh`).
//!
//! Ignored by default: it reads compiled definitions named by `VALUE_CONTRACT_DEFINITIONS`
//! (`name=path` entries separated by `:`), loads each with its last module as the main module, and
//! prints one `VALUE_CONTRACT {json}` line per definition with the check's verdict and counts. The
//! script compares the lines with `scripts/value-contract-corpus.toml`.
//!
//! The counts are the load's (`CheckScope::Gate`); the `full_` ones are those of the full check
//! (`CheckScope::All`), which also classifies the pairs that can change no claim. Each definition
//! also passes V9: the two verdicts admit the same claims and warn about the same pairs.

use std::time::Instant;

use k_rust_backend::{confluence::CheckScope, definition::BackendDefinition, term::HeadRole};
use k_rust_kore::kore::parser::parse_definition;

#[test]
#[ignore = "reads compiled definitions named by VALUE_CONTRACT_DEFINITIONS; run by scripts/value-contract-corpus.sh"]
fn value_contract_corpus() {
    let entries = std::env::var("VALUE_CONTRACT_DEFINITIONS")
        .expect("VALUE_CONTRACT_DEFINITIONS names the definitions to load");
    for entry in entries.split(':').filter(|entry| !entry.is_empty()) {
        let (name, path) = entry.split_once('=').expect("each entry is name=path");
        let text = std::fs::read_to_string(path)
            .unwrap_or_else(|error| panic!("{name}: cannot read {path}: {error}"));
        let syntax = parse_definition(&text).unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let main = syntax
            .modules
            .last()
            .expect("a definition has a module")
            .name
            .clone();
        let started = Instant::now();
        // Internalization recurses over the definition's terms: give it the stack a deep
        // definition needs.
        let (definition, seconds, full) = std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(move || {
                let definition = BackendDefinition::internalize(&syntax, &main)?;
                let seconds = started.elapsed().as_secs_f64();
                // The full check (`CheckScope::All`), for V9 and for the pairs that withdraw no
                // claim, which the load's scope does not classify.
                let full = definition.value_claims_in_scope(CheckScope::All);
                Ok::<_, k_rust_backend::definition::DefinitionError>((definition, seconds, full))
            })
            .expect("the loading thread starts")
            .join()
            .expect("loading does not panic")
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let claims = definition.value_claims();
        let differences = claims.claim_differences(&full, &definition);
        assert!(
            differences.is_empty(),
            "{name}: V9: the load's scope and the full check differ: {differences:?}"
        );
        let counts = claims.counts();
        let heads = definition
            .symbols()
            .values()
            .filter(|symbol| symbol.attributes.head_role() == HeadRole::EquationHead)
            .map(|symbol| symbol.name.clone())
            .collect::<Vec<_>>();
        let tainted = claims.tainted_symbols();
        let tainted_heads = heads.iter().filter(|head| tainted.contains(head)).count();
        let line = serde_json::json!({
            "name": name,
            "load_seconds": seconds,
            "equations": counts.equations,
            "pairs": counts.pairs,
            "overlaps": counts.overlaps,
            "separated": counts.separated,
            "refuted": counts.refuted,
            "joined": counts.joined,
            "unjoined": claims.unjoined().len(),
            "relevant": claims.unjoined().iter().filter(|pair| pair.relevant()).count(),
            "violations": claims.violations().len(),
            "heads": heads.len(),
            "tainted_heads": tainted_heads,
            "tainted_symbols": tainted.len(),
            "several_matches": counts.several_matches,
            "families": counts.families,
            "confluent_families": counts.confluent_families,
            "relevant_equations": counts.relevant_equations,
            "skipped": counts.skipped,
            "full_pairs": full.counts().pairs,
            "full_unjoined": full.unjoined().len(),
            "full_tainted_symbols": full.tainted_symbols().len(),
        });
        println!("VALUE_CONTRACT {line}");
    }
}
