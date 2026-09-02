//! Sentence-local fresh variable names.
//!
//! Java's fresh-name passes restart their counters at the pass/sentence boundary and compare
//! `KVariable`s by name alone. Keeping that policy here prevents two variables with the same name
//! but different sorts from reaching one KORE axiom.

use std::collections::BTreeSet;

use crate::{definition::Sentence, kast::Term};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct FreshNames {
    used: BTreeSet<String>,
    counter: usize,
}

impl FreshNames {
    /// Reserve every variable name occurring below the supplied roots, regardless of its sort.
    pub(crate) fn for_terms<'a>(roots: impl IntoIterator<Item = &'a Term>) -> Self {
        let mut fresh = Self::default();
        for root in roots {
            root.visit_preorder(&mut |term| {
                if let Term::Variable { name, .. } = term {
                    fresh.reserve(name.clone());
                }
            });
        }
        fresh
    }

    /// Reserve every variable name occurring in a sentence's term-bearing fields.
    pub(crate) fn for_sentence(sentence: &Sentence) -> Self {
        match sentence {
            Sentence::Rule {
                body,
                requires,
                ensures,
                ..
            }
            | Sentence::Claim {
                body,
                requires,
                ensures,
                ..
            } => Self::for_terms([body, requires, ensures]),
            Sentence::Context { body, requires, .. }
            | Sentence::ContextAlias { body, requires, .. } => Self::for_terms([body, requires]),
            Sentence::Configuration { body, ensures, .. } => Self::for_terms([body, ensures]),
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::Bubble { .. } => Self::default(),
        }
    }

    pub(crate) fn reserve(&mut self, name: impl Into<String>) {
        self.used.insert(name.into());
    }

    pub(crate) fn contains(&self, name: &str) -> bool {
        self.used.contains(name)
    }

    /// Mint the first unused `{prefix}{n}`, advancing past rejected candidates like Java.
    pub(crate) fn mint(&mut self, prefix: &str) -> String {
        loop {
            let candidate = format!("{prefix}{}", self.counter);
            self.counter += 1;
            if !self.contains(&candidate) {
                self.reserve(candidate.clone());
                return candidate;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::kast::Sort;

    use super::*;

    #[test]
    fn mint_skips_used_names_and_advances_the_counter_like_java() {
        let terms = [
            Term::Variable {
                name: "_Gen0".into(),
                sort: Some(Sort::new("Int")),
            },
            Term::Variable {
                name: "_Gen2".into(),
                sort: Some(Sort::new("K")),
            },
        ];
        let mut fresh = FreshNames::for_terms(&terms);

        assert_eq!(fresh.mint("_Gen"), "_Gen1");
        assert_eq!(fresh.mint("_Gen"), "_Gen3");
    }
}
