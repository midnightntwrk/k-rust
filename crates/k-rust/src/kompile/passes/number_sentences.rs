//! ```toml algorithm
//! id = "kompile.sentences.number"
//! name = "stable numbering of sentences by normalized digest"
//! sites = ["number_sentences", "number_sentences_pass", "number_sentence", "unique_id_text"]
//! variable = "N = normalized sentence and term nodes; h = term height"
//! counters = ["KompileSentenceCopies"]
//!
//! [[cost]]
//! mode = "one definition"
//! bound = "O(N x h)"
//! ```
//!
//! This transformation pass assigns UNIQUE_ID attributes to rules and claims and records no origins.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Assign stable `UNIQUE_ID` identifiers to rules and claims.
//!
//! An identifier is a digest of the sentence's text in the identifier format of K's `kompile`, so
//! that a definition compiled by either compiler names a sentence alike; the comments below that
//! describe the hashed text describe that format. Terms are written in the identifier layout
//! (`Printer::print_identifier_term`), which is fixed apart from the readable KAST layout, so that
//! making printed KAST easier to read back does not rename sentences.
#![deny(clippy::wildcard_enum_match_arm)]

use std::{collections::BTreeMap, convert::Infallible, fmt::Write};

use serde_json::Value;
use sha3::{Digest, Sha3_256};

use crate::definition::AttributeKey;
use crate::{
    definition::{Attributes, Definition, Sentence},
    kast::{Term, binding, printer::Printer},
};

const PRESERVED_ATTRIBUTES: [AttributeKey; 7] = [
    AttributeKey::Concrete,
    AttributeKey::Symbolic,
    AttributeKey::Owise,
    AttributeKey::Priority,
    AttributeKey::Simplification,
    AttributeKey::Anywhere,
    AttributeKey::NonExecutable,
];

/// Give every rule and claim its `UNIQUE_ID` attribute.
pub fn number_sentences(definition: &Definition) -> Definition {
    super::super::pipeline::run_standalone(definition, number_sentences_pass, None)
        .unwrap_or_else(|error| match error {})
}

pub(crate) fn number_sentences_pass(
    input: &super::super::pipeline::PassInput<'_>,
    _: &mut super::super::pipeline::PipelineState,
) -> Result<Definition, Infallible> {
    let mut output = input.definition.clone();
    for module in &mut output.modules {
        for sentence in &mut module.local_sentences {
            // Only rules and claims without an identifier change. The kind is decided before
            // taking a mutable sentence, which copies a shared one, so every other sentence stays
            // shared.
            match &**sentence {
                Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. }
                    if !attributes.has(AttributeKey::UniqueId) =>
                {
                    number_sentence(crate::definition::sentence_mut(sentence));
                }
                Sentence::SyntaxSort { .. }
                | Sentence::SortSynonym { .. }
                | Sentence::SyntaxLexical { .. }
                | Sentence::Production { .. }
                | Sentence::SyntaxAssociativity { .. }
                | Sentence::SyntaxPriority { .. }
                | Sentence::ContextAlias { .. }
                | Sentence::Context { .. }
                | Sentence::Rule { .. }
                | Sentence::Claim { .. }
                | Sentence::Configuration { .. }
                | Sentence::Bubble { .. } => {}
            }
        }
    }
    Ok(output)
}

pub(crate) fn number_sentence(sentence: &mut Sentence) {
    let (Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. }) = sentence else {
        return;
    };
    if attributes.has(AttributeKey::UniqueId) {
        return;
    }

    let semantic_attributes = Attributes::from_pairs(
        PRESERVED_ATTRIBUTES
            .into_iter()
            .filter_map(|key| attributes.value(key).map(|value| (key, value.clone()))),
    );
    let text = unique_id_text(sentence, &semantic_attributes);
    let digest = Sha3_256::digest(text.as_bytes());
    let mut id = String::with_capacity(digest.len() * 2);
    for byte in digest {
        write!(id, "{byte:02x}").expect("writing to a string cannot fail");
    }
    match sentence {
        Sentence::Rule { attributes, .. } | Sentence::Claim { attributes, .. } => {
            attributes.set(AttributeKey::UniqueId, Value::String(id));
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("guard selected a rule or claim"),
    }
}

pub(crate) fn unique_id_text(sentence: &Sentence, attributes: &Attributes) -> String {
    match sentence {
        Sentence::Rule {
            body,
            requires,
            ensures,
            ..
        } => {
            let [body, requires, ensures] = normalize_rule_variables(body, requires, ensures)
                .map(|term| Printer::new().print_identifier_term(&term));
            format!(
                "rule {body} requires {requires} ensures {ensures} {}",
                format_attributes(attributes)
            )
        }
        // A claim's text is hashed without variable normalization, unlike a rule's, so its
        // identifier changes with its variable names; this is part of the identifier format.
        Sentence::Claim {
            body,
            requires,
            ensures,
            ..
        } => {
            let [body, requires, ensures] =
                [body, requires, ensures].map(|term| Printer::new().print_identifier_term(term));
            format!(
                "claim {body} requires {requires} ensures {ensures} {}",
                format_attributes(attributes)
            )
        }
        Sentence::SyntaxSort { .. }
        | Sentence::SortSynonym { .. }
        | Sentence::SyntaxLexical { .. }
        | Sentence::Production { .. }
        | Sentence::SyntaxAssociativity { .. }
        | Sentence::SyntaxPriority { .. }
        | Sentence::ContextAlias { .. }
        | Sentence::Context { .. }
        | Sentence::Configuration { .. }
        | Sentence::Bubble { .. } => unreachable!("only rules and claims are numbered"),
    }
}

fn normalize_rule_variables(body: &Term, requires: &Term, ensures: &Term) -> [Term; 3] {
    let mut numbering = Numbering::default();
    [body, requires, ensures].map(|term| numbering.term(term))
}

/// The numbering of a rule's variables by first occurrence, which makes the hashed text the same
/// for every renaming of the rule's variables.
///
/// A variable is numbered `_<n>` at its first occurrence in preorder over body, `requires` and
/// `ensures`. A free variable is identified by its name alone, whatever sorts its occurrences are
/// annotated with: a name denotes one variable of the sentence. A quantifier's variable is its
/// own (`kast::binding`): it is numbered afresh at the quantifier, and the occurrences the
/// quantifier binds take that number, so a binder that shadows a variable of the rule, or reuses
/// the name of another binder, is numbered apart from it.
#[derive(Default)]
struct Numbering {
    /// The number of each free name met so far.
    free: BTreeMap<String, String>,
    /// The names bound around the current term with their numbers, innermost last.
    bound: Vec<(String, String)>,
    /// The numbers given so far.
    counter: usize,
}

impl Numbering {
    fn fresh(&mut self) -> String {
        let name = format!("_{}", self.counter);
        self.counter += 1;
        name
    }

    fn variable(&mut self, name: &str) -> String {
        if let Some((_, number)) = self.bound.iter().rev().find(|(bound, _)| bound == name) {
            return number.clone();
        }
        if let Some(number) = self.free.get(name) {
            return number.clone();
        }
        let number = self.fresh();
        self.free.insert(name.to_owned(), number.clone());
        number
    }

    // Invariant: `self.counter` numbers have been given, each to the first occurrence of a free
    // name (`self.free`) or to a quantifier's bound name; `self.bound` holds the names bound
    // around `term`; each call recurses into the immediate subterms of `term`.
    fn term(&mut self, term: &Term) -> Term {
        let normalized = if let Some(quantifier) = binding::quantifier(term) {
            let scope = self.bound.len();
            for name in quantifier.bound() {
                let number = self.fresh();
                self.bound.push((name.to_owned(), number));
            }
            let binder = self.term(quantifier.binder);
            let body = self.term(quantifier.body);
            self.bound.truncate(scope);
            Term::Apply {
                label: normalize_label(quantifier.label),
                arguments: vec![binder, body],
            }
        } else {
            match term.unannotated() {
                Term::Variable { name, sort } => Term::Variable {
                    name: self.variable(name),
                    sort: sort.clone(),
                },
                Term::Rewrite { left, right } => Term::Rewrite {
                    left: Box::new(self.term(left)),
                    right: Box::new(self.term(right)),
                },
                Term::As { pattern, alias } => Term::As {
                    pattern: Box::new(self.term(pattern)),
                    alias: Box::new(self.term(alias)),
                },
                Term::Sequence(items) => {
                    Term::Sequence(items.iter().map(|item| self.term(item)).collect())
                }
                Term::Apply { label, arguments } => Term::Apply {
                    label: normalize_label(label),
                    arguments: arguments
                        .iter()
                        .map(|argument| self.term(argument))
                        .collect(),
                },
                Term::InjectedLabel(label) => Term::InjectedLabel(normalize_label(label)),
                Term::Token { token, sort } => Term::Token {
                    token: token.clone(),
                    sort: sort.clone(),
                },
                Term::Annotated { .. } => unreachable!("unannotated strips metadata"),
            }
        };
        match term.metadata().cloned() {
            Some(metadata) => normalized.with_metadata(metadata),
            None => normalized,
        }
    }
}

fn normalize_label(label: &crate::kast::Label) -> crate::kast::Label {
    // A conjunction that strictness added to a condition is chosen only after macro expansion
    // (`ml_constructs`), after this stage; the identifier hashes it as the Bool conjunction, so
    // it does not depend on when in the pipeline the choice is made.
    if let Some(hashed) = crate::kompile::ml_constructs::hashed_label(label) {
        return hashed;
    }
    // The hashed text omits instantiated production parameters, but keeps the explicit
    // polymorphic placeholder carried by generated subsort and ML sentences.
    if label.parameters.iter().any(|sort| sort.is_rigid_variable()) {
        crate::kast::Label::with_parameters(
            label.name.clone(),
            label
                .parameters
                .iter()
                .map(|sort| crate::kast::Sort::new(sort.name.clone()))
                .collect(),
        )
    } else {
        crate::kast::Label::new(label.name.clone())
    }
}

fn format_attributes(attributes: &Attributes) -> String {
    if attributes.is_empty() {
        return String::new();
    }
    let values = attributes
        .wire_entries()
        .map(|(key, value)| match value {
            Value::String(value) if value.is_empty() => key.to_owned(),
            Value::String(value) => format!("{key}({value})"),
            Value::Null => key.to_owned(),
            value @ Value::Bool(_)
            | value @ Value::Number(_)
            | value @ Value::Array(_)
            | value @ Value::Object(_) => format!("{key}({value})"),
        })
        .collect::<Vec<_>>();
    format!("[{}]", values.join(", "))
}

#[cfg(test)]
#[allow(clippy::wildcard_enum_match_arm)]
mod tests {
    use super::*;
    use crate::kast::{Label, Sort};

    fn truth() -> Term {
        Term::Token {
            token: "true".into(),
            sort: Sort::new("Bool"),
        }
    }

    /// A conjunction strictness added and left pending until macro expansion is hashed as the
    /// Bool conjunction, so the identifier does not depend on when it is chosen.
    #[test]
    fn a_pending_condition_conjunction_hashes_as_the_bool_conjunction() {
        let make = |requires: Term| Sentence::Rule {
            body: Term::apply("f", vec![Term::variable("X")]),
            requires,
            ensures: truth(),
            attributes: Attributes::default(),
        };
        let test = || Term::apply("isKResult", vec![Term::variable("X")]);
        let pending = crate::kompile::ml_constructs::conjoin_condition(test(), truth());
        assert!(!matches!(&pending, Term::Apply { label, .. } if label.name == "_andBool_"));
        assert_eq!(
            unique_id_text(&make(pending), &Attributes::default()),
            unique_id_text(
                &make(Term::apply("_andBool_", vec![test(), truth()])),
                &Attributes::default()
            )
        );
    }

    #[test]
    fn alpha_equivalent_rules_have_the_same_hash_text() {
        let make = |name: &str| Sentence::Rule {
            body: Term::apply("f", vec![Term::variable(name)]),
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        };
        assert_eq!(
            unique_id_text(&make("X"), &Attributes::default()),
            unique_id_text(&make("Y"), &Attributes::default())
        );
    }

    /// A quantifier binds its own variable, so a binder that shadows a variable of its rule, or
    /// reuses the name of a sibling binder, is numbered as a variable of its own: the rule and
    /// its alpha-variant with that binder renamed apart hash alike.
    #[test]
    fn shadowing_and_repeated_binders_hash_as_their_own_variables() {
        let exists =
            |name: &str, body: Term| Term::apply("#Exists", vec![Term::variable(name), body]);
        let g = |name: &str| Term::apply("g", vec![Term::variable(name)]);
        let rule = |requires: Term| Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::apply("f", vec![Term::variable("Y")])),
                right: Box::new(Term::variable("Y")),
            },
            requires,
            ensures: truth(),
            attributes: Attributes::default(),
        };
        let text = |sentence: &Sentence| unique_id_text(sentence, &Attributes::default());
        // `#Exists Y . g(Y)` beside the left side's `Y`.
        assert_eq!(
            text(&rule(exists("Y", g("Y")))),
            text(&rule(exists("Z", g("Z"))))
        );
        // Two sibling binders of one name.
        let siblings = |second: &str| {
            rule(Term::apply(
                "h",
                vec![exists("X", g("X")), exists(second, g(second))],
            ))
        };
        assert_eq!(text(&siblings("X")), text(&siblings("Z")));
        // A nested binder of the enclosing binder's name.
        let nested = |inner: &str| {
            rule(exists(
                "X",
                Term::apply("h", vec![g("X"), exists(inner, g(inner))]),
            ))
        };
        assert_eq!(text(&nested("X")), text(&nested("Z")));
    }

    /// The hashed text writes a rewrite between sequences in the identifier layout, without the
    /// groups the readable KAST layout puts around a sequence operand, so a rule's identifier
    /// does not depend on how readable KAST is laid out.
    #[test]
    fn unique_id_text_writes_sequence_rewrites_in_the_identifier_layout() {
        let item = |name: &str| Term::apply(name, Vec::new());
        let sentence = Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(Term::Sequence(vec![item("a"), Term::variable("K")])),
                right: Box::new(Term::Sequence(vec![item("b"), Term::variable("K")])),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        };
        assert_eq!(
            unique_id_text(&sentence, &Attributes::default()),
            "rule a(.KList)~>_0=>b(.KList)~>_0 requires #token(\"true\",\"Bool\") ensures \
             #token(\"true\",\"Bool\") "
        );
    }

    #[test]
    fn unique_id_text_numbers_rule_variables_by_first_occurrence() {
        let sentence = Sentence::Rule {
            body: Term::Rewrite {
                // `B` occurs before `A`, so numbering by first occurrence and numbering by name
                // give different texts.
                left: Box::new(Term::Apply {
                    label: Label::new("f"),
                    arguments: vec![Term::variable("B"), Term::variable("A")],
                }),
                right: Box::new(Term::variable("A")),
            },
            requires: truth(),
            ensures: truth(),
            attributes: Attributes::default(),
        };
        assert_eq!(
            unique_id_text(&sentence, &Attributes::default()),
            "rule f(_0,_1)=>_1 requires #token(\"true\",\"Bool\") ensures #token(\"true\",\"Bool\") "
        );
    }
}
