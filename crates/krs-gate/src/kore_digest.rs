//! Canonical digest of a kompiled reference KORE definition.
//!
//! Source locations are rewritten only inside the K frontend's `Source` attributes.
//! Compiler-generated `Var'Unds'GenN` names are alpha-normalized per sentence through the comparator's variable walker.
//! The K frontend emits a module's `subsort` axioms in hash-set order, which varies between runs of the same input,
//! so those axioms are sorted among the positions they occupy.
//! Other variable names, the order of every other sentence, and all sentence structure remain significant.

use std::{error::Error, fs, path::Path};

use k_rust::kore::{
    ast::{Attributes, KoreString, Pattern, Sentence},
    parser::parse_definition,
    printer::Printer,
};
use sha2::{Digest, Sha256};

use crate::kore_compare::{alpha_normalize_generated_variables, sentence_attributes_mut};

const SOURCE_ATTRIBUTE: &str = "org'Stop'kframework'Stop'attributes'Stop'Source";
const SUBSORT_ATTRIBUTE: &str = "subsort";

/// Return the SHA-256 digest of structurally normalized, pretty-printed KORE.
///
/// # Errors
///
/// Fails for invalid KORE, a nonabsolute semantics path, or missing source evidence.
pub fn digest(source: &str, semantics: &Path) -> Result<String, Box<dyn Error>> {
    if !semantics.is_absolute() {
        return Err("semantics path must be absolute".into());
    }
    let semantics = semantics.to_str().ok_or("semantics path must be UTF-8")?;
    let mut definition = parse_definition(source)?;
    let printer = Printer::pretty(100);
    let mut counts = SourceCounts::default();
    rewrite_attributes(&mut definition.attributes, semantics, &mut counts)?;
    for module in &mut definition.modules {
        rewrite_attributes(&mut module.attributes, semantics, &mut counts)?;
        for sentence in &mut module.sentences {
            rewrite_attributes(sentence_attributes_mut(sentence), semantics, &mut counts)?;
            alpha_normalize_generated_variables(sentence);
        }
        sort_subsort_axioms(&mut module.sentences, printer);
    }
    if counts.semantics == 0 {
        return Err("definition.kore does not record its semantics source".into());
    }
    if counts.builtin == 0 {
        return Err("definition.kore does not record K's builtin sources".into());
    }
    let canonical = printer.print_definition(&definition);
    Ok(format!("{:x}", Sha256::digest(canonical.as_bytes())))
}

/// Sort a module's `subsort` axioms by their printed form, keeping the positions they occupy.
fn sort_subsort_axioms(sentences: &mut [Sentence], printer: Printer) {
    let positions: Vec<usize> = sentences
        .iter()
        .enumerate()
        .filter(|(_, sentence)| is_subsort_axiom(sentence))
        .map(|(position, _)| position)
        .collect();
    let mut axioms: Vec<(String, Sentence)> = positions
        .iter()
        .map(|&position| {
            let sentence = sentences[position].clone();
            (printer.print_sentence(&sentence), sentence)
        })
        .collect();
    axioms.sort_by(|left, right| left.0.cmp(&right.0));
    for (position, (_, sentence)) in positions.into_iter().zip(axioms) {
        sentences[position] = sentence;
    }
}

fn is_subsort_axiom(sentence: &Sentence) -> bool {
    let Sentence::Axiom { attributes, .. } = sentence else {
        return false;
    };
    attributes.0.iter().any(|attribute| {
        matches!(attribute, Pattern::Application { symbol, .. } if symbol.name == SUBSORT_ATTRIBUTE)
    })
}

/// Read and digest one kompiled KORE definition.
///
/// # Errors
///
/// Fails when the input cannot be read or normalized.
pub fn digest_file(kore: &Path, semantics: &Path) -> Result<String, Box<dyn Error>> {
    digest(&fs::read_to_string(kore)?, semantics)
}

#[derive(Default)]
struct SourceCounts {
    semantics: usize,
    builtin: usize,
}

fn rewrite_attributes(
    attributes: &mut Attributes,
    semantics: &str,
    counts: &mut SourceCounts,
) -> Result<(), Box<dyn Error>> {
    for attribute in &mut attributes.0 {
        let Pattern::Application { symbol, arguments } = attribute else {
            continue;
        };
        if symbol.name != SOURCE_ATTRIBUTE {
            continue;
        }
        let [Pattern::String(value)] = arguments.as_mut_slice() else {
            return Err("Source attribute must contain one string".into());
        };
        let text = value.as_utf8()?;
        let Some(path) = text
            .strip_prefix("Source(")
            .and_then(|text| text.strip_suffix(')'))
        else {
            return Err("Source attribute has an unexpected value".into());
        };
        if path == semantics {
            *value = KoreString::from("Source(semantics.k)");
            counts.semantics += 1;
        } else if path.starts_with('/')
            && let Some((_, suffix)) = path.split_once("/include/kframework/")
        {
            *value = KoreString::from(format!("Source(k/include/kframework/{suffix})"));
            counts.builtin += 1;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::digest;
    use std::path::Path;

    fn definition(semantics: &str, install: &str, binder: &str, symbol: &str) -> String {
        format!(
            "[org'Stop'kframework'Stop'attributes'Stop'Source{{}}(\"Source({semantics})\")]\n\
             module M\n\
               sort SortInt{{}} [org'Stop'kframework'Stop'attributes'Stop'Source{{}}(\"Source({install}/include/kframework/builtin/domains.md)\")]\n\
               symbol Lblf{{}}(SortInt{{}}) : SortInt{{}} []\n\
               axiom{{}} \\exists{{SortInt{{}}}}({binder}:SortInt{{}}, {symbol}{{}}({binder}:SortInt{{}})) []\n\
             endmodule []\n"
        )
    }

    #[test]
    fn paths_and_generated_names_are_canonical_but_axioms_remain_significant() {
        let first = definition(
            "/tmp/a/semantics.k",
            "/nix/store/one-k",
            "Var'Unds'Gen1",
            "Lblf",
        );
        let second = definition("/tmp/b/semantics.k", "/opt/k", "Var'Unds'Gen7", "Lblf");
        let changed = definition("/tmp/b/semantics.k", "/opt/k", "Var'Unds'Gen7", "Lblg");
        let first_digest = digest(&first, Path::new("/tmp/a/semantics.k")).unwrap();
        assert_eq!(
            first_digest,
            digest(&second, Path::new("/tmp/b/semantics.k")).unwrap()
        );
        assert_ne!(
            first_digest,
            digest(&changed, Path::new("/tmp/b/semantics.k")).unwrap()
        );
    }

    #[test]
    fn subsort_axiom_order_is_canonical_but_other_order_remains_significant() {
        let subsort = |sort: &str| {
            format!(
                "  axiom{{R}} \\exists{{R}} (Val:SortKItem{{}}, \\equals{{SortKItem{{}}, R}} (Val:SortKItem{{}}, \
                 inj{{{sort}{{}}, SortKItem{{}}}} (From:{sort}{{}}))) [subsort{{{sort}{{}}, SortKItem{{}}}}()]\n"
            )
        };
        let module = |sentences: &[String]| {
            format!(
                "[org'Stop'kframework'Stop'attributes'Stop'Source{{}}(\"Source(/tmp/a/semantics.k)\")]\n\
                 module M\n\
                   sort SortA{{}} [org'Stop'kframework'Stop'attributes'Stop'Source{{}}(\"Source(/opt/k/include/kframework/builtin/domains.md)\")]\n\
                   sort SortB{{}} []\n\
                 {}\
                 endmodule []\n",
                sentences.concat()
            )
        };
        let symbol = |name: &str| format!("  symbol {name}{{}}(SortA{{}}) : SortB{{}} []\n");
        let semantics = Path::new("/tmp/a/semantics.k");
        let ordered = module(&[
            subsort("SortA"),
            subsort("SortB"),
            symbol("Lblf"),
            symbol("Lblg"),
        ]);
        let swapped = module(&[
            subsort("SortB"),
            subsort("SortA"),
            symbol("Lblf"),
            symbol("Lblg"),
        ]);
        let reordered = module(&[
            subsort("SortA"),
            subsort("SortB"),
            symbol("Lblg"),
            symbol("Lblf"),
        ]);
        let digest_of = |source: &str| digest(source, semantics).unwrap();
        assert_eq!(digest_of(&ordered), digest_of(&swapped));
        assert_ne!(digest_of(&ordered), digest_of(&reordered));
    }

    #[test]
    fn missing_semantics_source_fails_closed() {
        let source = definition("/tmp/a/semantics.k", "/opt/k", "Var'Unds'Gen1", "Lblf");
        let error = digest(&source, Path::new("/tmp/other.k")).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("does not record its semantics source")
        );
    }

    #[test]
    fn missing_builtin_source_fails_closed() {
        let source = definition("/tmp/a/semantics.k", "/opt/k", "Var'Unds'Gen1", "Lblf")
            .replace("/include/kframework/", "/other/");
        let error = digest(&source, Path::new("/tmp/a/semantics.k")).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("does not record K's builtin sources")
        );
    }
}
