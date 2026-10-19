//! This transformation pass renames variables in place and records no origins: a renamed
//! variable keeps its node's metadata, its location and origin included.
//! Its named `--timings` phase measures total cost; the shared pass scaffolding counts resolutions (`KompileResolveCalls`), copied sentences (`KompileSentenceCopies`), and partial orders built (`KompilePartialOrdersBuilt`), and `KompileSentencesTransformed` is added once per compile in `compile.rs`.
//!
//! Rename the bound variables of every sentence apart.
//!
//! A quantifier binds the variables of its binder in its body and nowhere else
//! ([`crate::kast::binding`]), so renaming a bound variable to a name its sentence does not use
//! gives the same sentence. After this stage every sentence is apart (invariant BC, checked at
//! every later stage boundary): no name is bound by two quantifiers, and no bound name is free in
//! the sentence or named by its attributes. A pass that maps names across a whole sentence
//! (semantic-cast bounds, macro substitution, fresh-constant offsets, sort injection, cell
//! concretization, term minimization, rule numbering) then reads each name as one variable,
//! whatever scope it occurs in.
//!
//! The stage runs first among the transformation stages, so every one of them reads apart
//! sentences, and the search-pattern route renames its pattern the same way
//! ([`rename_bound_apart_in_sentence`]).
//!
//! A quantifier keeps the name it binds when that name is free nowhere in the sentence, named by
//! none of its attributes (`concrete`, `symbolic`, `unboundVariables`), and bound by no earlier
//! quantifier in preorder over the sentence's terms; it renames it to a fresh name
//! (`kast::binding::Reservation::mint`, which keeps the sigil and the `_` prefix) otherwise.
//! This is the shared rule of `kast::binding::rename_apart_in_sentence`, with the attributes'
//! names counted as free (`rename_apart_in_sentence_beside`).
//! A sentence that is already apart is left unchanged.
//!
//! Until anonymity stops being read from spellings, a binder spelled as a resolved anonymous
//! variable (`_Gen` and digits, and the like) is left as it is: the passes that give those names
//! reserve every name of the sentence, so each such binder is already unique.
#![deny(clippy::wildcard_enum_match_arm)]

use std::collections::BTreeSet;
use std::convert::Infallible;

use crate::definition::{AttributeKey, Attributes, Definition, Sentence};
use crate::kast::Term;
use crate::kast::binding::{
    Reservation, quantifier, reads_as_resolved_anonymous, rename_apart_in_sentence_beside,
};

use super::super::pipeline::{PassInput, PassOutcome, PipelineState};

/// The attributes whose values name variables of their sentence.
const VARIABLE_NAMING_ATTRIBUTES: [AttributeKey; 3] = [
    AttributeKey::Concrete,
    AttributeKey::Symbolic,
    AttributeKey::UnboundVariables,
];

pub(crate) fn rename_bound_apart_pass(
    input: &PassInput<'_>,
    _: &mut PipelineState,
) -> Result<PassOutcome, Infallible> {
    let mut output: Option<Definition> = None;
    // Invariant: every sentence before (`module`, `index`) is apart in `output`, which exists
    // once one of them changed; each iteration renames one sentence.
    for (module, declared) in input.definition.modules.iter().enumerate() {
        for (index, sentence) in declared.local_sentences.iter().enumerate() {
            if !holds_quantifier(sentence) {
                continue;
            }
            let mut renamed = (**sentence).clone();
            if !rename_bound_apart_in_sentence(&mut renamed) {
                continue;
            }
            let output = output.get_or_insert_with(|| input.definition.clone());
            *crate::definition::sentence_mut(&mut output.modules[module].local_sentences[index]) =
                renamed;
        }
    }
    Ok(output.map_or(PassOutcome::Unchanged, PassOutcome::Changed))
}

/// Rename the bound variables of `sentence` apart (module documentation); whether any changed.
/// This is [`rename_apart_in_sentence_beside`] over the sentence's terms, with the names its
/// variable-naming attributes list as `named` and the resolved-anonymous spellings kept.
pub(crate) fn rename_bound_apart_in_sentence(sentence: &mut Sentence) -> bool {
    let named = attribute_variable_names(sentence.attributes());
    let terms = sentence.terms_mut().map(|(_, term)| term);
    !rename_apart_in_sentence_beside(
        terms,
        &named,
        reads_as_resolved_anonymous,
        &mut Reservation::new(),
    )
    .is_empty()
}

/// The variable names `attributes` mention: the comma-separated entries of `concrete`,
/// `symbolic` and `unboundVariables`.
pub(crate) fn attribute_variable_names(attributes: &Attributes) -> BTreeSet<String> {
    VARIABLE_NAMING_ATTRIBUTES
        .iter()
        .filter_map(|key| attributes.string(*key))
        .flat_map(|names| names.split(','))
        .map(str::trim)
        .filter(|name| !name.is_empty())
        .map(str::to_owned)
        .collect()
}

/// Whether a term of `sentence` holds a quantifier.
fn holds_quantifier(sentence: &Sentence) -> bool {
    sentence.terms().any(|(_, term)| {
        let mut found = false;
        term.visit_preorder(&mut |node: &Term| found |= quantifier(node).is_some());
        found
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exists(name: &str, body: Term) -> Term {
        Term::apply("#Exists", vec![Term::variable(name), body])
    }

    fn g(name: &str) -> Term {
        Term::apply("g", vec![Term::variable(name)])
    }

    fn rule(left: &str, requires: Term, attributes: Attributes) -> Sentence {
        Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(g(left)),
                right: Box::new(Term::variable(left)),
            },
            requires,
            ensures: Term::apply("true", Vec::new()),
            attributes,
        }
    }

    fn renamed(mut sentence: Sentence) -> (bool, Sentence) {
        let changed = rename_bound_apart_in_sentence(&mut sentence);
        (changed, sentence)
    }

    /// A binder that shadows a free variable, reuses a sibling binder's name, or is spelled like a
    /// name an attribute mentions, is renamed to a fresh name; the free variable, the first
    /// binder of a name and every other binder keep theirs.
    #[test]
    fn a_bound_name_that_occurs_elsewhere_in_its_sentence_is_renamed_fresh() {
        let (changed, shadowing) = renamed(rule(
            "X",
            exists("X", Term::apply("h", vec![g("X"), Term::variable("X0")])),
            Attributes::default(),
        ));
        assert!(changed);
        assert_eq!(
            shadowing,
            rule(
                "X",
                exists("X1", Term::apply("h", vec![g("X1"), Term::variable("X0")])),
                Attributes::default()
            )
        );

        let (changed, siblings) = renamed(rule(
            "Y",
            Term::apply("h", vec![exists("Z", g("Z")), exists("Z", g("Z"))]),
            Attributes::default(),
        ));
        assert!(changed);
        assert_eq!(
            siblings,
            rule(
                "Y",
                Term::apply("h", vec![exists("Z", g("Z")), exists("Z0", g("Z0"))]),
                Attributes::default()
            )
        );

        let mut attributes = Attributes::default();
        attributes.set(AttributeKey::Concrete, "Z".into());
        let (changed, named) = renamed(rule("Y", exists("Z", g("Z")), attributes.clone()));
        assert!(changed);
        assert_eq!(named, rule("Y", exists("Z0", g("Z0")), attributes));
    }

    /// A sentence already apart is unchanged, and so is a binder spelled as a resolved anonymous
    /// variable, which the passes minting those names keep unique.
    #[test]
    fn an_apart_sentence_and_a_resolved_anonymous_binder_are_left_as_they_are() {
        let apart = rule(
            "X",
            Term::apply("h", vec![exists("Y", g("Y")), exists("Z", g("Z"))]),
            Attributes::default(),
        );
        assert_eq!(renamed(apart.clone()), (false, apart));
        let generated = rule("_Gen1", exists("_Gen1", g("_Gen1")), Attributes::default());
        assert_eq!(renamed(generated.clone()), (false, generated));
    }
}
