//! This definition check traverses module sentences and terms linearly; callers supply derived catalogs and no dedicated counter is recorded.
//!
//! Function-symbol matching checks: where a rule's left-hand side may contain a function symbol.
//!
//! A function application on a left-hand side is read in one of two ways, decided by the kind
//! of rule, never by the position the application stands at:
//!
//! - **An equation** (a function rule, whose left-hand side is rooted at a `function`
//!   production, an `anywhere` rule, or a macro-like rule) is matched against the application it
//!   rewrites as written: its argument patterns are compared with the subject's arguments, not
//!   evaluated. An application of a computed symbol below its root would therefore match only a
//!   subject that spells the same application, never the value it computes, and the instance
//!   the evaluator could use would carry the definedness of an application nothing reduces. So
//!   below an equation's root only the collection constructors are admitted (the unit, element
//!   and concatenation of a `LIST`, `SET`, `MAP` or `BAG` sort, which build the collection value
//!   their arguments describe), and their arguments are checked like any other argument.
//! - **A rewrite rule** (or a context) reads a function application inside a key, value or
//!   element of a collection, or an operand of a collection's concatenation, by value: it
//!   matches the collection entry whose key or element equals the value the application
//!   computes once the variables in it are bound. That reading is the same at every argument of
//!   a collection constructor, and covers everything below it. Elsewhere on a rewrite rule's
//!   left-hand side a function application is rejected as before.
//!
//! `LIST.update` is not a collection constructor: an update `L[I <- V]` is a function of a list,
//! not a way to write one, so it is admitted on a left-hand side only where a function
//! application is (inside a collection argument of a rewrite rule).

use std::collections::BTreeSet;

use super::Sentence;
use super::labels::internal_labels;
use super::term_position::{TermPosition, positioned_children};
use crate::definition::AttributeKey;
use crate::definition::{LabelHead, ProductionCatalog, SortCatalog};
use crate::diagnostic::{Diagnostic, DiagnosticCode};
use crate::kast::{InternalLabel, Term};

/// The hooks of the collection constructors: the unit, element and concatenation of each
/// builtin collection sort.
const COLLECTION_CONSTRUCTOR_HOOKS: [&str; 12] = [
    "LIST.element",
    "LIST.concat",
    "LIST.unit",
    "SET.element",
    "SET.concat",
    "SET.unit",
    "MAP.element",
    "MAP.concat",
    "MAP.unit",
    "BAG.element",
    "BAG.concat",
    "BAG.unit",
];

pub fn check_functions(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    sorts: &SortCatalog<'_>,
) -> Vec<Diagnostic> {
    check_functions_with_internal_labels(
        sentences,
        productions,
        &internal_labels(productions, sorts),
    )
}

/// How a rule's left-hand side reads a function application below its root.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Reading {
    /// Not decided yet: the root application has not been visited.
    Undecided,
    /// An equation: argument patterns are matched as written.
    Equation,
    /// A rewrite rule or a context: a function application inside a collection argument is
    /// read by value.
    Rewrite,
}

/// The state of the walk of one sentence's body.
struct Walk<'a> {
    reading: Reading,
    internal_labels: &'a BTreeSet<String>,
    productions: &'a ProductionCatalog<'a>,
    sentence: &'a Sentence,
    diagnostics: &'a mut Vec<Diagnostic>,
}

/// [`check_functions`] against the internal labels of the module whose catalogs are supplied,
/// for a caller that checks one module's sentences in several calls and computes them once.
pub(crate) fn check_functions_with_internal_labels(
    sentences: &[&Sentence],
    productions: &ProductionCatalog<'_>,
    internal_labels: &BTreeSet<String>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for sentence in sentences {
        let (body, reading) = match sentence {
            Sentence::Rule {
                body, attributes, ..
            } if !attributes.has(AttributeKey::Simplification) => {
                let equation = attributes.has(AttributeKey::Anywhere)
                    || attributes.has_any(&AttributeKey::MACRO_LIKE);
                (
                    body,
                    if equation {
                        Reading::Equation
                    } else {
                        Reading::Undecided
                    },
                )
            }
            Sentence::Context { body, .. } | Sentence::ContextAlias { body, .. } => {
                (body, Reading::Rewrite)
            }
            Sentence::SyntaxSort { .. }
            | Sentence::SortSynonym { .. }
            | Sentence::SyntaxLexical { .. }
            | Sentence::Production { .. }
            | Sentence::SyntaxAssociativity { .. }
            | Sentence::SyntaxPriority { .. }
            | Sentence::Rule { .. }
            | Sentence::Claim { .. }
            | Sentence::Configuration { .. }
            | Sentence::Bubble { .. } => continue,
        };
        let mut walk = Walk {
            reading,
            internal_labels,
            productions,
            sentence,
            diagnostics: &mut diagnostics,
        };
        let mut at_top = true;
        walk.visit_term(body, TermPosition::BODY, &mut at_top, false);
    }
    diagnostics
}

impl Walk<'_> {
    // Invariant: `position` is the `TermPosition` of `term`, and `at_top` stays true only until
    // the first application other than `WithConfig` is visited; `by_value` holds inside an
    // argument of a collection constructor of a rewrite rule. Each recursive call, directly or
    // through `visit_arguments`, receives a strict subterm of `term`, so the size of the rule
    // body bounds the calls.
    fn visit_term(
        &mut self,
        term: &Term,
        position: TermPosition,
        at_top: &mut bool,
        by_value: bool,
    ) {
        let Term::Apply { label, .. } = term.unannotated() else {
            self.visit_arguments(term, position, at_top, by_value);
            return;
        };

        if label.is(InternalLabel::WithConfig) {
            self.visit_arguments(term, position, at_top, by_value);
            return;
        }

        let attributes = self.productions.attributes_for(&LabelHead::from(label));
        if self.internal_labels.contains(&label.name) || attributes.is_none() {
            if *at_top {
                *at_top = false;
                // A root that is no production (a cell fragment, a K sequence) is not an
                // equation's head.
                if self.reading == Reading::Undecided {
                    self.reading = Reading::Rewrite;
                }
            }
            self.visit_arguments(term, position, at_top, by_value);
            return;
        }

        let attributes = attributes.expect("checked above");
        let function = attributes.has(AttributeKey::Function);
        if *at_top {
            *at_top = false;
            if self.reading == Reading::Undecided {
                // The root of the left-hand side: a function rule is an equation of its root
                // symbol, any other rule rewrites the configuration around it.
                self.reading = if function && position.lhs {
                    Reading::Equation
                } else {
                    Reading::Rewrite
                };
            }
            let constructor = is_collection_constructor(attributes.string(AttributeKey::Hook));
            let by_value = self.reading == Reading::Rewrite && constructor;
            self.visit_arguments(term, position, at_top, by_value);
            return;
        }

        let constructor = is_collection_constructor(attributes.string(AttributeKey::Hook));
        if function && position.lhs && !by_value && !constructor {
            let message = if self.reading == Reading::Equation {
                format!(
                    "Illegal function symbol {} below the root of an equation's left-hand side: an equation matches its argument patterns as written, so this application would never match the value it computes. Bind the position to a variable and state its value in the `requires` clause, or add the `simplification` attribute if the rule is a lemma.",
                    label.name
                )
            } else {
                format!(
                    "Illegal function symbol {} on LHS of rule: a rewrite rule reads a function application by value only inside a key, value or element of a collection. Consider adding `simplification` attribute to the rule if this is intended.",
                    label.name
                )
            };
            self.diagnostics.push(Diagnostic::error(
                DiagnosticCode::IllegalFunctionOnLhs,
                message,
                self.sentence,
            ));
        }
        let by_value = by_value || (self.reading == Reading::Rewrite && constructor);
        self.visit_arguments(term, position, at_top, by_value);
    }

    fn visit_arguments(
        &mut self,
        term: &Term,
        position: TermPosition,
        at_top: &mut bool,
        by_value: bool,
    ) {
        for (child, child_position) in positioned_children(term, position) {
            self.visit_term(child, child_position, at_top, by_value);
        }
    }
}

/// Whether `hook` is the hook of a collection constructor.
fn is_collection_constructor(hook: Option<&str>) -> bool {
    hook.is_some_and(|hook| COLLECTION_CONSTRUCTOR_HOOKS.contains(&hook))
}
