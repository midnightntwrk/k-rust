//! The digest of a finding's name (the parent module's documentation, "The digest"): SHA-256,
//! truncated to 128 bits, over a version tag, the finding's kind, an inner pair's position, the
//! hook or precondition row it states, each of its compiled sentences, and the declarations of
//! the symbols those sentences (and the row) apply.
//!
//! A sentence is hashed by exclusion: every field of the internalized [`RewriteRule`] and of its
//! [`RuleAttributes`] is read, the two structs destructured without `..` so that a field added
//! later does not compile until it is either hashed or excluded here, and only these are
//! excluded:
//! - `label` and `unique_id`: what the name's readable part calls the sentence, not what it says;
//! - `origins`: the written source, location and place in its module, which every edit above the
//!   sentence moves;
//! - `computed_attributes`: what the load derived from the rule and the rest of the definition
//!   (variable sets, discharges, caches), not part of the sentence; the parts it is derived from
//!   are hashed, and the rest of the definition is deliberately not covered.
//!
//! The patterns (left-hand side, right-hand side, conditions) are hashed as their KORE
//! externalization, node by node in pre-order with each node's child count, so that the bytes
//! read back one pattern; each variable is renamed by its first occurrence in that walk, over the
//! whole sentence, so two sentences that differ by a renaming of variables have one digest.
//!
//! A symbol's declaration is its sort variables, argument sorts, result sort and every symbol
//! attribute the backend keeps ([`SymbolAttributes`](crate::term::SymbolAttributes), hashed by
//! its `Debug` text, which writes every field). The subsort and overload relations of the
//! mentioned sorts are not covered, nor is any equation other than the finding's own: every new
//! sort sits under `KItem`, so covering the relations would change every digest at an unrelated
//! edit.

use std::collections::{BTreeMap, BTreeSet};

use k_rust_kore::kore::ast as kore;
use sha2::{Digest as _, Sha256};

use crate::{
    definition::BackendDefinition,
    externalize,
    rule::{Concreteness, RewriteRule, RuleAttributes, RuleRhs},
    term::{
        Sort,
        names::{VariableProvenance, split_marker},
    },
};

/// The version of the digest's encoding: a change to what it reads, or how, changes every
/// digest, so the names of the previous version are refused as `changed` once.
pub const DIGEST_VERSION: &str = "k-rust-backend/finding-name/v1";

/// The bytes a digest is computed from, each field tagged and length-prefixed so that two
/// different encodings never write the same bytes.
pub(super) struct Writer {
    hasher: Sha256,
    /// The symbols the encoded sentences and row apply, KORE names.
    symbols: BTreeSet<String>,
}

impl Writer {
    pub(super) fn new(kind: &str) -> Self {
        let mut writer = Self {
            hasher: Sha256::new(),
            symbols: BTreeSet::new(),
        };
        writer.text(b'v', DIGEST_VERSION);
        writer.text(b'k', kind);
        writer
    }

    fn bytes(&mut self, tag: u8, bytes: &[u8]) {
        self.hasher.update([tag]);
        self.hasher.update((bytes.len() as u64).to_le_bytes());
        self.hasher.update(bytes);
    }

    pub(super) fn text(&mut self, tag: u8, text: &str) {
        self.bytes(tag, text.as_bytes());
    }

    pub(super) fn number(&mut self, tag: u8, number: u64) {
        self.bytes(tag, &number.to_le_bytes());
    }

    /// A symbol the finding names outside its sentences (a precondition row's), whose
    /// declaration [`Self::finish`] hashes.
    pub(super) fn symbol(&mut self, name: &str) {
        self.symbols.insert(name.to_owned());
    }

    /// One compiled sentence (the module documentation).
    pub(super) fn rule(&mut self, rule: &RewriteRule) {
        let RewriteRule {
            lhs,
            lhs_alternative,
            rhs,
            requires,
            ensures,
            attributes,
            // Derived from the rest of the rule and the definition (the module documentation).
            computed_attributes: _,
            existentials,
        } = rule;
        let RuleAttributes {
            priority,
            // What the readable part calls the sentence.
            label: _,
            unique_id: _,
            simplification,
            preserves_definedness,
            concreteness,
            smt_lemma,
            executable,
            // Provenance: source, location and place in the module.
            origins: _,
            overload,
        } = attributes;
        let mut names = Renaming::default();
        self.text(b'S', "sentence");
        self.pattern(&externalize::term(lhs), &mut names);
        match lhs_alternative {
            Some(alternative) => self.number(b'a', *alternative as u64),
            None => self.text(b'a', "one"),
        }
        let condition_sort = Sort::variable("R");
        match rhs {
            RuleRhs::Term(term) => {
                self.text(b'r', "term");
                self.pattern(&externalize::term(term), &mut names);
            }
            RuleRhs::Disjunction(alternatives) => {
                self.text(b'r', "disjunction");
                self.number(b'n', alternatives.len() as u64);
                for alternative in alternatives {
                    self.pattern(&externalize::term(&alternative.term), &mut names);
                    self.number(b'n', alternative.ensures.len() as u64);
                    for predicate in alternative.ensures.iter() {
                        self.pattern(
                            &externalize::ml_pattern(predicate, &condition_sort),
                            &mut names,
                        );
                    }
                }
            }
            RuleRhs::Top => self.text(b'r', "top"),
            RuleRhs::Bottom => self.text(b'r', "bottom"),
            RuleRhs::Predicates(predicates) => {
                self.text(b'r', "predicates");
                self.number(b'n', predicates.len() as u64);
                for predicate in predicates {
                    self.pattern(
                        &externalize::ml_pattern(predicate, &condition_sort),
                        &mut names,
                    );
                }
            }
        }
        for (tag, condition) in [(b'q', requires), (b'e', ensures)] {
            self.number(tag, condition.len() as u64);
            for predicate in condition.iter() {
                self.pattern(
                    &externalize::ml_pattern(predicate, &condition_sort),
                    &mut names,
                );
            }
        }
        let mut renamed = existentials
            .iter()
            .map(|variable| {
                (
                    names.name(false, &externalize::external_variable_name(&variable.name)),
                    externalize::sort(&variable.sort).to_string(),
                )
            })
            .collect::<Vec<_>>();
        renamed.sort();
        self.number(b'x', renamed.len() as u64);
        for (name, sort) in renamed {
            self.text(b'x', &name);
            self.text(b's', &sort);
        }
        self.number(b'p', u64::from(*priority));
        self.number(b'b', u64::from(*simplification));
        self.number(b'b', u64::from(*preserves_definedness));
        self.number(b'b', u64::from(*smt_lemma));
        self.number(b'b', u64::from(*executable));
        match concreteness {
            Concreteness::Unconstrained => self.text(b'c', "unconstrained"),
            Concreteness::All(kind) => self.text(b'c', &format!("all {kind:?}")),
            Concreteness::Some(constrained) => {
                // A constraint names a rule variable by its name without the provenance marker
                // and by its sort: renamed as that variable is.
                let externals = rule
                    .computed_attributes
                    .variables
                    .iter()
                    .map(|variable| {
                        let unmarked = split_marker(
                            &variable.name,
                            &[VariableProvenance::Rule, VariableProvenance::Equation],
                        )
                        .1
                        .into_owned();
                        (
                            (unmarked, variable.sort),
                            externalize::external_variable_name(&variable.name),
                        )
                    })
                    .collect::<BTreeMap<_, _>>();
                let mut constraints = constrained
                    .iter()
                    .map(|((name, sort), kind)| {
                        let renamed = externals
                            .get(&(name.to_string(), *sort))
                            .and_then(|external| names.existing(false, external))
                            .unwrap_or_else(|| format!("unread {name}"));
                        (
                            renamed,
                            externalize::sort(sort).to_string(),
                            format!("{kind:?}"),
                        )
                    })
                    .collect::<Vec<_>>();
                constraints.sort();
                self.text(b'c', "some");
                self.number(b'n', constraints.len() as u64);
                for (name, sort, kind) in constraints {
                    self.text(b'x', &name);
                    self.text(b's', &sort);
                    self.text(b'c', &kind);
                }
            }
        }
        match overload {
            Some((greater, lesser)) => {
                self.text(b'o', greater);
                self.text(b'o', lesser);
                self.symbols.insert(greater.to_string());
                self.symbols.insert(lesser.to_string());
            }
            None => self.text(b'o', "none"),
        }
    }

    /// `pattern` node by node in pre-order, each with its child count, variables renamed by
    /// `names`; every applied symbol is remembered for [`Self::finish`].
    fn pattern(&mut self, pattern: &kore::Pattern, names: &mut Renaming) {
        let mut work = vec![pattern];
        while let Some(node) = work.pop() {
            let children = k_rust_kore::kore::walk::children(node);
            self.node(node, names);
            self.number(b'n', children.len() as u64);
            work.extend(children.into_iter().rev());
        }
    }

    fn node(&mut self, node: &kore::Pattern, names: &mut Renaming) {
        use kore::Pattern;
        match node {
            Pattern::String(text) => self.bytes(1, text.as_bytes()),
            Pattern::Variable(variable) => {
                self.text(2, "variable");
                self.variable(variable, names);
            }
            Pattern::Application { symbol, .. } => {
                self.text(3, &symbol.to_string());
                self.symbols.insert(symbol.name.clone());
            }
            Pattern::Top { sort } => self.text(4, &sort.to_string()),
            Pattern::Bottom { sort } => self.text(5, &sort.to_string()),
            Pattern::And { sort, .. } => self.text(6, &sort.to_string()),
            Pattern::Or { sort, .. } => self.text(7, &sort.to_string()),
            Pattern::Not { sort, .. } => self.text(8, &sort.to_string()),
            Pattern::Next { sort, .. } => self.text(9, &sort.to_string()),
            Pattern::Implies { sort, .. } => self.text(10, &sort.to_string()),
            Pattern::Iff { sort, .. } => self.text(11, &sort.to_string()),
            Pattern::Rewrites { sort, .. } => self.text(12, &sort.to_string()),
            Pattern::Exists { sort, variable, .. } => {
                self.text(13, &sort.to_string());
                self.variable(variable, names);
            }
            Pattern::Forall { sort, variable, .. } => {
                self.text(14, &sort.to_string());
                self.variable(variable, names);
            }
            Pattern::Mu { variable, .. } => {
                self.text(15, "mu");
                self.variable(variable, names);
            }
            Pattern::Nu { variable, .. } => {
                self.text(16, "nu");
                self.variable(variable, names);
            }
            Pattern::Ceil {
                operand_sort,
                result_sort,
                ..
            } => {
                self.text(17, &operand_sort.to_string());
                self.text(17, &result_sort.to_string());
            }
            Pattern::Floor {
                operand_sort,
                result_sort,
                ..
            } => {
                self.text(18, &operand_sort.to_string());
                self.text(18, &result_sort.to_string());
            }
            Pattern::Equals {
                operand_sort,
                result_sort,
                ..
            } => {
                self.text(19, &operand_sort.to_string());
                self.text(19, &result_sort.to_string());
            }
            Pattern::In {
                operand_sort,
                result_sort,
                ..
            } => {
                self.text(20, &operand_sort.to_string());
                self.text(20, &result_sort.to_string());
            }
            Pattern::DomainValue { sort, value } => {
                self.text(21, &sort.to_string());
                self.bytes(21, value.as_bytes());
            }
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                ..
            } => {
                self.text(22, &format!("{associativity:?}"));
                self.text(22, &symbol.to_string());
                self.symbols.insert(symbol.name.clone());
            }
        }
    }

    fn variable(&mut self, variable: &kore::Variable, names: &mut Renaming) {
        let set = variable.kind == kore::VariableKind::Set;
        let name = names.name(set, &variable.name);
        self.text(b'x', &name);
        self.text(b's', &variable.sort.to_string());
    }

    /// The digest: the declarations of every symbol remembered, then the hash, truncated to 128
    /// bits, as 32 lowercase hexadecimal digits.
    pub(super) fn finish(mut self, definition: &BackendDefinition) -> String {
        let symbols = std::mem::take(&mut self.symbols);
        self.number(b'n', symbols.len() as u64);
        for name in &symbols {
            self.text(b'y', name);
            match definition.symbols().get(name.as_str()) {
                Some(symbol) => {
                    let crate::term::Symbol {
                        name: _,
                        sort_variables,
                        argument_sorts,
                        result_sort,
                        attributes,
                    } = &**symbol;
                    self.number(b'n', sort_variables.len() as u64);
                    for variable in sort_variables {
                        self.text(b'v', variable);
                    }
                    self.number(b'n', argument_sorts.len() as u64);
                    for sort in argument_sorts {
                        self.text(b's', &externalize::sort(sort).to_string());
                    }
                    self.text(b's', &externalize::sort(result_sort).to_string());
                    self.text(b'a', &format!("{attributes:?}"));
                }
                None => self.text(b'u', "undeclared"),
            }
        }
        let hash: [u8; 32] = self.hasher.finalize().into();
        hash[..16]
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect()
    }
}

/// The renaming of one sentence's variables by first occurrence: the `n`th distinct variable
/// met is `V{n}` (`@V{n}` for a set variable).
#[derive(Default)]
struct Renaming(BTreeMap<(bool, String), usize>);

impl Renaming {
    fn name(&mut self, set: bool, name: &str) -> String {
        let next = self.0.len();
        let index = *self.0.entry((set, name.to_owned())).or_insert(next);
        if set {
            format!("@V{index}")
        } else {
            format!("V{index}")
        }
    }

    fn existing(&self, set: bool, name: &str) -> Option<String> {
        self.0.get(&(set, name.to_owned())).map(|index| {
            if set {
                format!("@V{index}")
            } else {
                format!("V{index}")
            }
        })
    }
}
