//! Which `Id` tokens an author spec module's grammar lexes (KF-041).
//!
//! K parses a proof module's sentences with that module's grammar. `Id` has
//! no rule-grammar lexical syntax of its own (its identifier regex exists only
//! for program parsing), so an identifier in a spec-module claim lexes only
//! through a token production the module sees: a terminal token, or a regex
//! token of the definition such as upstream IMP-VERIFICATION's
//! `r"\$[a-zA-Z0-9\_]+"`.

use std::collections::BTreeSet;

use krs_ir::GrammarProductionItemKind;

/// The `Id` token productions a spec module sees.
pub(crate) struct IdLexicon {
    terminals: BTreeSet<String>,
    /// Each regex token, or `None` when KRS cannot evaluate its regex.
    regexes: Vec<Option<regex::Regex>>,
}

impl IdLexicon {
    /// Collects the single item of each visible `Id` token production.
    pub(crate) fn new<'a, S: 'a>(
        productions: impl IntoIterator<
            Item = impl IntoIterator<Item = &'a GrammarProductionItemKind<S>>,
        >,
    ) -> Self {
        let mut terminals = BTreeSet::new();
        let mut regexes = Vec::new();
        for items in productions {
            for item in items {
                match item {
                    GrammarProductionItemKind::Terminal { text } => {
                        terminals.insert(text.clone());
                    }
                    // A lookaround guard is K-specific; such a token is not evaluated.
                    GrammarProductionItemKind::RegexTerminal {
                        precede_regex,
                        regex,
                        follow_regex,
                    } => regexes.push(
                        (precede_regex.is_none() && follow_regex.is_none())
                            .then(|| regex::Regex::new(&format!("^(?:{regex})$")).ok())
                            .flatten(),
                    ),
                    GrammarProductionItemKind::NonTerminal { .. } => {}
                }
            }
        }
        Self { terminals, regexes }
    }

    /// Whether some visible token production may lex `value`; a regex KRS
    /// cannot evaluate is assumed to.
    pub(crate) fn may_lex(&self, value: &str) -> bool {
        self.terminals.contains(value)
            || self
                .regexes
                .iter()
                .any(|regex| regex.as_ref().is_none_or(|regex| regex.is_match(value)))
    }

    /// Whether some visible token production certainly lexes `value`, so it
    /// may be printed bare.
    pub(crate) fn lexes(&self, value: &str) -> bool {
        self.terminals.contains(value)
            || self
                .regexes
                .iter()
                .any(|regex| regex.as_ref().is_some_and(|regex| regex.is_match(value)))
    }
}

#[cfg(test)]
mod tests {
    use super::IdLexicon;
    use krs_ir::GrammarProductionItemKind;

    #[test]
    fn terminals_and_anchored_regexes_lex_identifiers() {
        let regex = GrammarProductionItemKind::<()>::RegexTerminal {
            precede_regex: None,
            regex: r"\$[a-zA-Z0-9_]+".to_owned(),
            follow_regex: None,
        };
        let terminal = GrammarProductionItemKind::<()>::Terminal {
            text: "x".to_owned(),
        };
        let lexicon = IdLexicon::new([vec![&regex], vec![&terminal]]);
        assert!(lexicon.lexes("$n"));
        assert!(lexicon.lexes("x"));
        assert!(!lexicon.lexes("y"));
        assert!(!lexicon.lexes("a$n"));
        assert!(!lexicon.may_lex("y"));
        let unknown = GrammarProductionItemKind::<()>::RegexTerminal {
            precede_regex: None,
            regex: r"(?<![a-z])q".to_owned(),
            follow_regex: None,
        };
        let lexicon = IdLexicon::new([vec![&unknown]]);
        assert!(lexicon.may_lex("y"));
        assert!(!lexicon.lexes("y"));
    }
}
