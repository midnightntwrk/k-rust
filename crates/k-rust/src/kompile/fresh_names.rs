//! ```toml algorithm
//! id = "kompile.fresh_names.mint"
//! name = "sentence-local fresh-name generation"
//! sites = ["FreshNames::for_terms", "FreshNames::for_sentence", "FreshNames::mint", "FreshNames::reserve"]
//! variable = "R = reserved names; C = colliding candidates"
//! counters = []
//! no_counter = "sentence-local fresh-name generation has no dedicated counter"
//!
//! [[cost]]
//! mode = "reservation by for_terms or for_sentence"
//! bound = "O(R log R)"
//!
//! [[cost]]
//! mode = "one name"
//! bound = "O((C + 1) x log R)"
//! ```
//!
//! Fresh-name generation reserves existing names and retries monotonically increasing suffixes.
//! Each mint takes at most O(reserved names + 1) attempts; no dedicated counter.
//!
//! Sentence-local fresh variable names.
//!
//! A fresh name need be unique only within its sentence, so counters restart at each pass and
//! sentence. Names are compared by name alone, whatever their sorts, which prevents two variables
//! with the same name but different sorts from reaching one KORE axiom.

use std::collections::BTreeSet;

use crate::kore::ast::VariableKind;
use crate::{definition::Sentence, kast::Term};

/// The exact pre-encoding identity of a variable minted by a compilation pass.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct GeneratedVariableIdentity {
    pub kind: VariableKind,
    pub name: String,
}

impl GeneratedVariableIdentity {
    pub fn element(name: impl Into<String>) -> Self {
        Self {
            kind: VariableKind::Element,
            name: name.into(),
        }
    }

    pub fn set(name: impl Into<String>) -> Self {
        Self {
            kind: VariableKind::Set,
            name: name.into(),
        }
    }
}

/// The sigil of a variable name: `?` (existential), `!` (fresh) or `@` (set variable), or `""`
/// for none.
pub(crate) fn sigil(name: &str) -> &'static str {
    match name.chars().next() {
        Some('?') => "?",
        Some('!') => "!",
        Some('@') => "@",
        _ => "",
    }
}

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
        Self::for_terms(sentence.terms().map(|(_, term)| term))
    }

    pub(crate) fn reserve(&mut self, name: impl Into<String>) {
        self.used.insert(name.into());
    }

    pub(crate) fn contains(&self, name: &str) -> bool {
        self.used.contains(name)
    }

    /// Mint a variable the compiler introduces in the place of a variable with sigil `sigil`
    /// (`""`, `?`, `!` or `@`, [`sigil`]): `{sigil}_Gen{n}`, which keeps the role the sigil gives
    /// (existential, fresh, or a set variable), with the identity that records it as minted.
    pub(crate) fn mint_generated(&mut self, sigil: &str) -> GeneratedVariableIdentity {
        let name = self.mint(&format!("{sigil}_Gen"));
        if sigil == "@" {
            GeneratedVariableIdentity::set(name)
        } else {
            GeneratedVariableIdentity::element(name)
        }
    }

    /// Mint the first unused `{prefix}{n}` from the counter on; the counter also advances past the
    /// rejected candidates.
    pub(crate) fn mint(&mut self, prefix: &str) -> String {
        // Invariant: every smaller suffix considered by this call was already reserved and the
        // counter increases once per attempt, so an unused name appears within |used| + 1 tries.
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
    fn mint_skips_used_names_and_advances_the_counter_past_them() {
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
