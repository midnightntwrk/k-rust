//! The text of a token production read as program text in a rule or configuration grammar.
//!
//! A token production with a nonterminal, such as `syntax Toks ::= Names [token]`, denotes the
//! token whose text is the text of its phrase (`build_packed_term`): `a , b` is the `Toks` token
//! `a , b`. A program spells such a phrase with the module's own syntax only, so every token of
//! the sort is the text of a phrase of that syntax. A rule or configuration grammar adds its own
//! constructs below the module's sorts (variables, configuration variables, `#token` literals,
//! casts, rewrites, brackets), and a phrase read through one of them would make a token of the
//! construct's spelling: `T:Toks` would be the token `T`, `$PGM` the token `$PGM`. Neither
//! spelling is a value a program can produce, and the construct itself (a variable to bind, a
//! configuration variable to read) would be lost. So in those grammars each nonterminal of the
//! module's own token productions is recognized at a copy of its sort that derives program text
//! only ([`Grammar::read_token_text_as_program_text`]).
//!
//! The pass is O(P x I) for the P productions of the copied sorts and their I items, run once
//! per rule or configuration grammar.

use std::collections::BTreeMap;

use crate::kast::Sort;

use super::{Grammar, Item};

impl Grammar {
    /// Recognize each nonterminal of every program-text token production at the program-text
    /// copy of its sort, so that the parse forest never holds a token whose text is read
    /// through a construct the grammar adds to the module's syntax.
    ///
    /// The copy of a sort `S` derives what the program-text productions of `S` derive, with each
    /// of their nonterminals recognized at its own copy in turn. A copied production keeps its
    /// declared result, items and attributes, and its node is that of the production it copies
    /// (`term_production`); only the sort ids it is recognized at change, as at a position
    /// widened to admit a rewrite (`Production::item_sort_ids`). The excluded readings are
    /// therefore never predicted, rather than built and discarded: a reading's provenance is
    /// gone once it is in the forest, where a variable under the unlabelled `Names ::= KBott`
    /// is a bare variable leaf and a `#token` literal a bare token.
    ///
    /// A token production the grammar adds itself, such as the variable's `#KVariable ::=
    /// #UpperId`, reads its own lexemes and is left as it is. A token production with a single
    /// regular-expression item has no nonterminal and no phrase; a single nonterminal of a
    /// lexical sort the module declares, as in `Id ::= #UpperId [token]`, reads that sort's
    /// program-text tokens, so a rule's `X` there is still the `Id` token `X`.
    ///
    /// Called once the rule or configuration grammar is complete, so that every production it
    /// adds is in place and no later pass widens a copied position.
    ///
    /// ```toml algorithm-site
    /// id = "parser.grammar.build"
    /// role = "part"
    /// sites = ["Grammar::read_token_text_as_program_text", "Grammar::program_text_sort_id"]
    /// ```
    pub(in crate::inner) fn read_token_text_as_program_text(&mut self) {
        let phrases = self
            .productions
            .iter()
            .enumerate()
            .filter(|(_, production)| {
                production.token && production.program_text && production.nonterminals > 0
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if phrases.is_empty() {
            return;
        }
        self.invalidate_prediction_analysis();
        self.relation_index = std::sync::OnceLock::new();
        let mut copies = BTreeMap::new();
        let mut pending = Vec::new();
        for phrase in phrases {
            self.recognize_items_as_program_text(phrase, &mut copies, &mut pending);
        }
        while let Some((original, copy)) = pending.pop() {
            let members = self.by_result[original]
                .iter()
                .copied()
                .filter(|member| self.productions[*member].program_text)
                .collect::<Vec<_>>();
            for member in members {
                let index = self.productions.len();
                let mut production = self.productions[member].clone();
                production.result_id = copy;
                production.term_production = Some(production.term_production.unwrap_or(member));
                self.productions.push(production);
                self.by_result[copy].push(index);
                self.recognize_items_as_program_text(index, &mut copies, &mut pending);
            }
        }
        // A copied unary production lies on a productive cycle exactly when its original does.
        self.identify_productive_unary_cycles();
    }

    /// Recognize each nonterminal of `production` at the program-text copy of its declared sort.
    fn recognize_items_as_program_text(
        &mut self,
        production: usize,
        copies: &mut BTreeMap<usize, usize>,
        pending: &mut Vec<(usize, usize)>,
    ) {
        for position in 0..self.productions[production].items.len() {
            let Item::NonTerminal(sort) = &self.productions[production].items[position] else {
                continue;
            };
            let sort = sort.clone();
            let copy = self.program_text_sort_id(&sort, copies, pending);
            self.productions[production].item_sort_ids[position] = Some(copy);
        }
    }

    /// The id of the program-text copy of `sort`, registered and queued for its productions the
    /// first time it is asked for.
    fn program_text_sort_id(
        &mut self,
        sort: &Sort,
        copies: &mut BTreeMap<usize, usize>,
        pending: &mut Vec<(usize, usize)>,
    ) -> usize {
        let original = self.intern_sort(sort);
        if let Some(copy) = copies.get(&original) {
            return *copy;
        }
        let copy = self.intern_sort(&program_text_sort(sort));
        copies.insert(original, copy);
        pending.push((original, copy));
        copy
    }
}

/// The program-text copy of `sort`. No declared sort name has a `#` after its first character,
/// so the copy is no sort of the definition (as the `Ne#` and `#Terminator` sorts of a program
/// list are none).
fn program_text_sort(sort: &Sort) -> Sort {
    Sort::with_parameters(
        format!("{}#ProgramText", sort.name),
        sort.parameters.clone(),
    )
}
