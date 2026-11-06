//! `warning[krs::analysis::skipped-operand]`: where a value or a condition depends on an operand
//! that `&&`, `||`, `bool::and`, `bool::or`, `bool::implies` or `kequal::ite` skips, and the
//! operand may have no value.
//!
//! The findings are k-rust's analysis of the loaded definition ([`krs_exec::skipped_operand`]);
//! this module places each at the operator the author wrote, drops what a `skipped_operand =
//! "reason"` key silences or `krs::analysis::dead-guard` already reports, warns at each key that
//! silences nothing, and words the warning by the operator.

use std::cell::Cell;
use std::collections::BTreeSet;
use std::fmt::Write as _;

use krs_diagnostic::{Diagnostic, Label, Location, Severity, codes};
use krs_exec::skipped_operand::{Anchor, Part, SkippedOperand, Through};
use krs_ir::{ApplicationRef, ProductionAttribute, SourceRange};
use krs_ir_levels::{
    DefinitionIr, DefinitionSentence, DefinitionTerm, DefinitionTermKind, RuleBodyRef, RuleSentence,
};

use super::PreparedDefinition;

/// A `skipped_operand = "reason"` key and what it silences.
struct Key {
    /// The key's location.
    location: Location,
    /// What it silences.
    target: Target,
    /// Whether it silenced a finding.
    used: Cell<bool>,
}

/// What a [`Key`] silences: every finding anchored at a sentence the author wrote as an equation
/// of the function with this KORE symbol (its body's branches, its table's rows, its
/// `#[k::equation]` fns), what a local function k-rust generates from one included.
enum Target {
    Function(String),
}

/// The `skipped-operand` and `stale-skipped-operand` warnings of `findings`, the findings of
/// `prepared`'s definition loaded on the `native-rust` route, in a fixed order.
pub(super) fn warnings(
    prepared: &PreparedDefinition,
    findings: &[SkippedOperand],
) -> Vec<Diagnostic> {
    let definition = prepared.lowered.definition();
    let keys = keys(prepared);
    let dead_guards = prepared
        .sort_test_warnings
        .iter()
        .filter(|warning| warning.code == codes::analysis::DEAD_GUARD)
        .filter_map(|warning| match &warning.primary.location {
            Location::Source(range) => Some(range.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let index = krs_ir_levels::k_surface::DefinitionIndex::new(definition);
    let mut warnings = Vec::new();
    let mut seen = BTreeSet::new();
    for finding in findings {
        let sentence = finding
            .anchor
            .as_ref()
            .and_then(|anchor| sentence(definition, anchor));
        // The function the anchor is an equation of, as the author wrote it: there its body's
        // branches are the fix and its key silences.
        let function = sentence.and_then(|sentence| own_function(&index, sentence));
        if let Some(function) = &function
            && silenced(&keys, function)
        {
            continue;
        }
        let located = sentence.and_then(|sentence| locate(&index, sentence, finding));
        // An operator KRS inserted is the test it writes before a conjunct of a condition, where
        // a skipped conjunct and an undefined one both leave the condition false; it shows in a
        // value position only where k-rust lifts a `let` of the condition into a function, whose
        // value is the condition's.
        if located.as_ref().is_some_and(|located| located.inserted) {
            continue;
        }
        if finding.part == Part::Condition
            && let Some(located) = &located
            && dead_guards.iter().any(|guard| {
                located
                    .operand_ranges
                    .iter()
                    .any(|range| contains(range, guard))
            })
        {
            continue;
        }
        // An operator in the prelude is reported at the sentence's application of the prelude
        // function that holds it.
        let applied = match (&finding.through, sentence) {
            (Some(Through::Builtin { function, .. }), Some(sentence)) => {
                applied_at(sentence, function)
            }
            _ => None,
        };
        let warning = render(finding, located.as_ref(), applied, function.is_some());
        // Two findings the analysis tells apart by their KORE operand can locate at one node.
        let identity = format!(
            "{:?}{:?}{}",
            warning.primary.location, finding.through, warning.message
        );
        if seen.insert(identity) {
            warnings.push(warning);
        }
    }
    for key in &keys {
        if !key.used.get() {
            let mut warning = Diagnostic::error(
                codes::analysis::STALE_SKIPPED_OPERAND,
                "`skipped_operand` states that a value may depend on an operand `&&`, `||` or `kequal::ite` skips, but no operand of this item is one that may have no value",
                key.location.clone(),
            )
            .with_help("remove `skipped_operand`");
            warning.severity = Severity::Warning;
            warnings.push(warning);
        }
    }
    warnings
}

/// Every `skipped_operand` key of `prepared`'s definition, each on a function's production.
fn keys(prepared: &PreparedDefinition) -> Vec<Key> {
    let definition = prepared.lowered.definition();
    let mut keys = Vec::new();
    // A function's key is a Semantic IR production attribute, which lowering consumes; the
    // production's KORE symbol is its Definition IR production's, lowered from the same item.
    for production in prepared
        .semantic
        .modules()
        .iter()
        .flat_map(krs_ir_levels::SemanticModule::productions)
    {
        for attribute in production.attributes() {
            let ProductionAttribute::SkippedOperand { origin, .. } = attribute else {
                continue;
            };
            let symbol = definition
                .modules()
                .iter()
                .flat_map(krs_ir_levels::DefinitionModule::sentences)
                .find_map(|sentence| match sentence {
                    DefinitionSentence::Production(lowered)
                        if lowered.origin().key() == production.origin().key()
                            || sentence.item() == Some(production.id()) =>
                    {
                        Some(krs_k_rust::kore_label(lowered.symbol().emitted_name()))
                    }
                    _ => None,
                });
            keys.push(Key {
                location: location(origin.origin().exact_authored_range()),
                target: Target::Function(symbol.unwrap_or_default()),
                used: Cell::new(false),
            });
        }
    }
    keys
}

/// Whether a key of `keys` silences a finding anchored at an equation of `function`, marking the
/// key used.
fn silenced(keys: &[Key], function: &str) -> bool {
    let mut silenced = false;
    for key in keys {
        let Target::Function(symbol) = &key.target;
        if function == symbol {
            key.used.set(true);
            silenced = true;
        }
    }
    silenced
}

/// The KORE symbol of the function `sentence` is an equation of: the head of its left-hand side,
/// an application of a declared function; `None` for a sentence of another kind (a rule, a
/// simplification).
fn own_function(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    sentence: &RuleSentence,
) -> Option<String> {
    if !matches!(sentence.kind(), krs_ir::SentenceKind::Equation) {
        return None;
    }
    let RuleBodyRef::Term(rewrite) = sentence.relational_body() else {
        return None;
    };
    match rewrite.from().kind() {
        DefinitionTermKind::Application {
            application: ApplicationRef::Declared(declared),
            ..
        } => index.symbol_name(declared).map(krs_k_rust::kore_label),
        _ => None,
    }
}

/// The Definition IR rule sentence `anchor` names.
fn sentence<'d>(definition: &'d DefinitionIr, anchor: &Anchor) -> Option<&'d RuleSentence> {
    definition
        .modules()
        .iter()
        .flat_map(krs_ir_levels::DefinitionModule::sentences)
        .find_map(|sentence| match sentence {
            DefinitionSentence::Rule(rule) if rule.origin().key() == anchor.origin.key() => {
                Some(rule)
            }
            _ => None,
        })
}

/// The operator node a finding names in its sentence, and the skipped operand's parts.
struct Located {
    /// The operator application's authored range (its head: the operator token, or the call's
    /// path).
    node: SourceRange,
    /// The range to label as having no value: the application of the finding's term in the
    /// skipped operand, else the operand's own.
    term: Option<SourceRange>,
    /// Every exact authored range in the skipped operand.
    operand_ranges: Vec<SourceRange>,
    /// Whether the author wrote the operator as notation (`a && b`, `a || b`): an application's
    /// range is its head, and the first operand's head comes before an infix operator but after a
    /// call's path.
    notation: bool,
    /// Whether KRS inserted the node (the test it writes before a conjunct of a condition).
    inserted: bool,
}

/// The node of `sentence` the finding's operator is: among the applications of a builtin with
/// the finding's operator hook whose skipped operand applies the finding's term, in the order the
/// analysis enumerates the emitted sentence's witnesses ([`sentence_terms`], each in post-order),
/// the one at the finding's occurrence, else the first; else the only application with that
/// hook.
fn locate(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    sentence: &RuleSentence,
    finding: &SkippedOperand,
) -> Option<Located> {
    let mut candidates = Vec::new();
    for term in sentence_terms(sentence) {
        postorder(term, &mut |node| {
            if let DefinitionTermKind::Application {
                application: ApplicationRef::Builtin(operation),
                arguments,
                ..
            } = node.kind()
                && operation.spec().k_hook == Some(finding.operator_hook.as_str())
                && let Some(range) = node.origin().origin().exact_authored_range()
            {
                let operand = arguments.get(finding.position);
                let term = operand.and_then(|operand| term_range(index, operand, finding));
                let inserted = node.origin().origin().inserted().is_some();
                candidates.push((term, range, operand, arguments.first(), inserted));
            }
        });
    }
    let preferred = candidates
        .iter()
        .filter(|(term, ..)| term.is_some())
        .collect::<Vec<_>>();
    let chosen = preferred
        .get(finding.occurrence)
        .or_else(|| preferred.first())
        .copied()
        .or(match candidates.as_slice() {
            [only] => Some(only),
            _ => None,
        })?;
    let (term, node, operand, first, inserted) = chosen;
    let mut operand_ranges = Vec::new();
    if let Some(operand) = operand {
        preorder(operand, &mut |part| {
            operand_ranges.extend(part.origin().origin().exact_authored_range());
        });
    }
    let first = first.and_then(|first| first.origin().origin().exact_authored_range());
    Some(Located {
        node: node.clone(),
        term: term
            .as_ref()
            .and_then(|term| term.range.clone())
            .or_else(|| {
                operand.and_then(|operand| operand.origin().origin().exact_authored_range())
            }),
        operand_ranges,
        notation: first.is_some_and(|first| first.start_byte < node.start_byte),
        inserted: *inserted,
    })
}

/// The first application in `term` (in preorder) that is the finding's term (module
/// documentation of [`krs_exec::skipped_operand`]): an application of its head symbol whose
/// arguments that are applications have the term's arguments' heads. It is given as its exact
/// authored range, which a node KRS rewrote may lack; `None` when `term` holds no such
/// application.
fn term_range(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    term: &DefinitionTerm,
    finding: &SkippedOperand,
) -> Option<TermNode> {
    let mut found = None;
    preorder(term, &mut |node| {
        if found.is_some() {
            return;
        }
        let (matches, arguments): (bool, Vec<&DefinitionTerm>) = match node.kind() {
            DefinitionTermKind::Application {
                application,
                arguments,
                ..
            } => (
                is_symbol(
                    index,
                    application,
                    &finding.term_symbol,
                    finding.term_hook.as_deref(),
                ),
                arguments.iter().collect(),
            ),
            // A collection operation is a term of its own kind, named by its hook.
            DefinitionTermKind::Map(operands) => (
                operands.operation().spec().k_hook == finding.term_hook.as_deref(),
                operands.operands().collect(),
            ),
            DefinitionTermKind::List(operands) => (
                operands.operation().spec().k_hook == finding.term_hook.as_deref(),
                operands.operands().collect(),
            ),
            DefinitionTermKind::Set(operands) => (
                operands.operation().spec().k_hook == finding.term_hook.as_deref(),
                operands.operands().collect(),
            ),
            _ => (false, Vec::new()),
        };
        if matches
            && arguments
                .iter()
                .zip(&finding.term_arguments)
                .all(
                    |(argument, head)| match (head, argument_head(index, argument)) {
                        (Some(head), Some(written)) => *head == written,
                        _ => true,
                    },
                )
        {
            found = Some(TermNode {
                range: node.origin().origin().exact_authored_range(),
            });
        }
    });
    found
}

/// Whether `application` is the KORE symbol `symbol` (a builtin by its label, or by `hook`).
fn is_symbol(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    application: &krs_ir_levels::DefinitionApplicationRef,
    symbol: &str,
    hook: Option<&str>,
) -> bool {
    match application {
        ApplicationRef::Builtin(operation) => {
            krs_k_rust::kore_label(operation.spec().k_label) == symbol
                || (hook.is_some() && operation.spec().k_hook == hook)
        }
        ApplicationRef::Declared(declared) => index
            .symbol_name(declared)
            .is_some_and(|name| krs_k_rust::kore_label(name) == symbol),
        ApplicationRef::Generated(_) => false,
    }
}

/// The KORE head symbol of `term` when it is a declared application (a builtin's label need not
/// spell its KORE symbol, so it tells nothing apart here), or its value, marked `\dv:`, when it is
/// a literal.
fn argument_head(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    term: &DefinitionTerm,
) -> Option<String> {
    match term.kind() {
        DefinitionTermKind::Application {
            application: ApplicationRef::Declared(declared),
            ..
        } => index.symbol_name(declared).map(krs_k_rust::kore_label),
        DefinitionTermKind::Token { value } => Some(format!("\\dv:{value}")),
        _ => None,
    }
}

/// The authored range of the first application in `sentence` (in preorder) of the builtin
/// operation with the K label `label`.
fn applied_at(sentence: &RuleSentence, label: &str) -> Option<SourceRange> {
    let mut found = None;
    for term in sentence_terms(sentence) {
        preorder(term, &mut |node| {
            if found.is_none()
                && let DefinitionTermKind::Application {
                    application: ApplicationRef::Builtin(operation),
                    ..
                } = node.kind()
                && operation.spec().k_label == label
            {
                found = node.origin().origin().exact_authored_range();
            }
        });
    }
    found
}

/// An application of a finding's term in its skipped operand ([`term_range`]).
struct TermNode {
    /// Its exact authored range, which a node KRS rewrote may lack.
    range: Option<SourceRange>,
}

/// The terms of a rule sentence in the order its emitted sentence holds them, as the analysis
/// enumerates its witnesses: its `requires` conditions, its left-hand side and its function
/// context's cells, its right-hand side, then its `ensures` conditions (a configuration rule's
/// cells hold both sides, in cell order).
fn sentence_terms(sentence: &RuleSentence) -> Vec<&DefinitionTerm> {
    let mut terms = Vec::new();
    if let Some(condition) = sentence.requires() {
        terms.extend(condition.terms());
    }
    let context = sentence.function_context().into_iter().flat_map(|context| {
        context
            .cells()
            .cells()
            .iter()
            .map(krs_ir::FixedCellPattern::pattern)
    });
    match sentence.relational_body() {
        RuleBodyRef::Term(rewrite) => {
            terms.push(rewrite.from());
            terms.extend(context);
            terms.push(rewrite.to());
        }
        RuleBodyRef::Configuration { body, .. } => {
            for part in body.parts() {
                terms.extend(part.terms());
            }
            terms.extend(context);
        }
        RuleBodyRef::Predicate(body) => {
            terms.extend(body.lhs().terms());
            terms.extend(context);
            terms.extend(body.rhs().terms());
        }
    }
    if let Some(condition) = sentence.ensures() {
        terms.extend(condition.terms());
    }
    terms
}

/// Visits `term` and its subterms in preorder.
fn preorder<'t>(term: &'t DefinitionTerm, visit: &mut impl FnMut(&'t DefinitionTerm)) {
    visit(term);
    for child in children(term) {
        preorder(child, visit);
    }
}

/// Visits `term` and its subterms in post-order.
fn postorder<'t>(term: &'t DefinitionTerm, visit: &mut impl FnMut(&'t DefinitionTerm)) {
    for child in children(term) {
        postorder(child, visit);
    }
    visit(term);
}

/// The direct subterms of `term`, in argument order.
fn children(term: &DefinitionTerm) -> Vec<&DefinitionTerm> {
    match term.kind() {
        DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => Vec::new(),
        DefinitionTermKind::Application { arguments, .. } => arguments.iter().collect(),
        DefinitionTermKind::KSequence { items, .. } => items.iter().collect(),
        DefinitionTermKind::Map(operands) => operands.operands().collect(),
        DefinitionTermKind::List(operands) => operands.operands().collect(),
        DefinitionTermKind::Set(operands) => operands.operands().collect(),
        DefinitionTermKind::Cell { children, .. } => children.iter().collect(),
        DefinitionTermKind::Rewrite { from, to } => vec![from.as_ref(), to.as_ref()],
        DefinitionTermKind::As { pattern, .. } => vec![pattern.as_ref()],
        DefinitionTermKind::Or { alternatives } => alternatives.iter().collect(),
        DefinitionTermKind::Matches {
            subject, pattern, ..
        } => vec![subject.as_ref(), pattern.as_ref()],
        DefinitionTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => vec![pattern.as_ref(), value.as_ref(), body.as_ref()],
    }
}

fn contains(outer: &SourceRange, inner: &SourceRange) -> bool {
    outer.file == inner.file
        && outer.start_byte <= inner.start_byte
        && inner.end_byte <= outer.end_byte
}

fn location(range: Option<SourceRange>) -> Location {
    range.map_or(Location::None, Location::Source)
}

/// How an operator reads: its written name, the operand it skips, when, the value a skipping
/// backend gives, and the branching form that means what a skipping backend computes.
struct Wording {
    written: &'static str,
    /// The operands' names in [`Self::branching`].
    operands: &'static str,
    skipped: &'static str,
    when: &'static str,
    skipping_value: &'static str,
    branching: &'static str,
}

/// The wording of `hook` at `position`, written as notation or as a call.
fn wording(hook: &str, position: usize, notation: bool) -> Wording {
    let boolean = |written, when, skipping_value, branching| Wording {
        written,
        operands: "`left` and `right` its operands",
        skipped: "its right operand",
        when,
        skipping_value,
        branching,
    };
    match (hook, position) {
        ("BOOL.andThen", _) => boolean(
            if notation { "&&" } else { "bool::and_then" },
            "its left operand is `false`",
            "`false`",
            "if left { right } else { false }",
        ),
        ("BOOL.orElse", _) => boolean(
            if notation { "||" } else { "bool::or_else" },
            "its left operand is `true`",
            "`true`",
            "if left { true } else { right }",
        ),
        ("BOOL.and", _) => boolean(
            "bool::and",
            "its left operand is `false`",
            "`false`",
            "if left { right } else { false }",
        ),
        ("BOOL.or", _) => boolean(
            "bool::or",
            "its left operand is `true`",
            "`true`",
            "if left { true } else { right }",
        ),
        ("BOOL.implies", _) => boolean(
            "bool::implies",
            "its left operand is `false`",
            "`true`",
            "if left { right } else { true }",
        ),
        ("KEQUAL.ite", 1) => Wording {
            written: "kequal::ite",
            operands: "`c`, `t` and `e` its operands",
            skipped: "its `then` operand",
            when: "its condition is `false`",
            skipping_value: "its `else` operand",
            branching: "if c { t } else { e }",
        },
        _ => Wording {
            written: "kequal::ite",
            operands: "`c`, `t` and `e` its operands",
            skipped: "its `else` operand",
            when: "its condition is `true`",
            skipping_value: "its `then` operand",
            branching: "if c { t } else { e }",
        },
    }
}

/// The calls each notation stands for.
fn call_of(written: &str) -> Option<&'static str> {
    match written {
        "&&" => Some("bool::and_then"),
        "||" => Some("bool::or_else"),
        _ => None,
    }
}

/// The warning of one finding.
fn render(
    finding: &SkippedOperand,
    located: Option<&Located>,
    applied: Option<SourceRange>,
    function: bool,
) -> Diagnostic {
    let notation = located.is_some_and(|located| located.notation);
    let wording = wording(&finding.operator_hook, finding.position, notation);
    let written = wording.written;
    let mut message = format!(
        "`{written}` does not evaluate {} where {}, but keeps that operand's definedness, and the operand may have no value",
        wording.skipped, wording.when
    );
    let primary = match (located, applied, &finding.anchor) {
        (Some(located), _, _) => Location::Source(located.node.clone()),
        (None, Some(applied), _) => Location::Source(applied),
        (None, None, Some(anchor)) => location(anchor.origin.origin().exact_authored_range()),
        (None, None, None) => Location::None,
    };
    if located.is_none() {
        let _ = write!(
            message,
            ": the operand `{}` holds `{}`",
            finding.operand, finding.term
        );
    }
    if let Some(name) = &finding.sentence {
        let _ = write!(message, ", in the prelude's sentence {name}");
    }
    let mut warning = Diagnostic::error(codes::analysis::SKIPPED_OPERAND, message, primary);
    warning.severity = Severity::Warning;
    if let Some(term) = located.and_then(|located| located.term.clone()) {
        warning = warning
            .with_secondary(Label::new(Location::Source(term)).with_message("may have no value"));
    }
    let strict = call_of(written).map_or_else(
        || format!("`{written}` is one strict function"),
        |call| format!("`{written}` is `{call}`, one strict function"),
    );
    // An operator in the prelude is not the author's to rewrite: only the key is theirs.
    let prelude = matches!(finding.through, Some(Through::Builtin { .. }));
    match finding.part {
        Part::Result => {
            warning = warning.with_note(format!(
                "{strict}: where the operand has no value, the application has none on every KRS route, while a backend that returns the selected operand alone gives {}, so the K KRS emits means different things on different backends, and kink does not judge a run that reads it",
                wording.skipping_value
            ));
            warning = if prelude {
                warning
            } else if function {
                warning.with_help(format!(
                    "write a branching body, whose branches are separate equations, each with its own definedness: `{}`, with {}; where this is not the whole body, move it into a helper function whose body branches",
                    wording.branching, wording.operands
                ))
            } else {
                warning.with_help(
                    "write one rule per case, or move the expression into a function whose body branches",
                )
            };
        }
        Part::Condition => {
            // The operator need not be the condition: its value is one operand of the
            // condition's own connectives, so only what the operator gives can be stated.
            warning = warning.with_note(format!(
                "so the sentence's condition does not hold where the operand has no value, while a Rust reading of `{written}` gives {} where {}, and the condition is then what that value makes it; and kink does not judge a run that reads it",
                wording.skipping_value, wording.when
            ));
            if !prelude {
                warning = warning.with_help(
                    "write each case as a sentence of its own (a branch of the function's body, or a rule), each under its own condition",
                );
            }
        }
    }
    match &finding.through {
        Some(Through::Local { .. }) => {
            warning = warning.with_note(
                "the operator is in a local function k-rust generates from this sentence's `let` block or `k::matches!` test, which the sentence applies where the block stands",
            );
        }
        Some(Through::Generated { pass }) => {
            warning = warning.with_note(format!(
                "the operator is in a sentence k-rust's `{pass}` pass generated from this one"
            ));
        }
        Some(Through::Builtin { module, function }) => {
            warning = warning.with_note(format!(
                "the operator is in the prelude's `{function}` (module `{module}`), which this sentence applies, and which a definition does not rewrite"
            ));
        }
        None => {}
    }
    let or = if prelude { "" } else { "or " };
    if function {
        warning = warning.with_help(format!(
            "{or}state that the strict meaning is intended: `#[k::function(.., skipped_operand = \"..\")]`"
        ));
    } else if finding.anchor.is_some() {
        let or = if prelude { "" } else { "or, " };
        warning = warning.with_help(format!(
            "{or}to state that the strict meaning is intended, move the expression into a function, which takes `#[k::function(.., skipped_operand = \"..\")]`"
        ));
    }
    warning
}
