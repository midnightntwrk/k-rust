//! `warning[krs::analysis::skipped-operand]`: where a value or a condition depends on an operand
//! that `&&`, `||`, `bool::and`, `bool::or`, `bool::implies` or `kequal::ite` skips, and the
//! operand may have no value.
//!
//! The findings are k-rust's analysis of the loaded definition ([`krs_exec::skipped_operand`]);
//! this module places each at the operator the author wrote, drops what
//! `krs::analysis::dead-guard` already reports, then what a `skipped_operand = "reason"` key
//! silences, warns at each key that silences nothing (so also at one whose findings are all
//! dropped first: removing it changes no warning), and words the warning by the operator.
//!
//! A key silences the findings anchored at the sentences its item writes: a function's
//! (`#[k::function(..)]`) every equation of the function, a rule's (`#[k::rule(..)]`) or an
//! equation's (`#[k::equation(..)]`) the sentence it marks. The item is the one the finding's
//! origin names, so a key applies wherever its item's sentences are warned, a `let` block's
//! local function and an application of the prelude included.

use std::cell::Cell;
use std::collections::BTreeSet;
use std::fmt::Write as _;

use krs_diagnostic::{Diagnostic, Label, Location, Severity, codes};
use krs_exec::skipped_operand::{Anchor, Part, SkippedOperand, TermHead, Through};
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

/// What a [`Key`] silences.
enum Target {
    /// Every finding anchored at a sentence the author wrote as an equation of the function with
    /// this KORE symbol (its body's branches, its table's rows, its `#[k::equation]` fns), what a
    /// local function k-rust generates from one included.
    Function(String),
    /// Every finding anchored at a sentence the item (a `#[k::rule]` or `#[k::equation]` item, a
    /// clause of `k::rules!`, a row of `k::equations!`) writes: one whose origin names the item.
    Item(krs_ir::StableItemId),
}

/// The key the help of a finding offers: the one its anchor's item takes.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Keyable {
    /// An equation of a function, whose `#[k::function(..)]` takes it.
    Function,
    /// An equation the author wrote as an `#[k::equation]` fn or a `k::equations!` row, whose
    /// `#[k::equation(..)]` takes it, as its function's `#[k::function(..)]` does.
    Equation,
    /// A transition, whose `#[k::rule(..)]` takes it.
    Rule,
    /// A sentence no item writes that takes the key (a constant's, an initializer's, a
    /// sentence a pass generated): the expression moves into a function.
    None,
}

/// The `skipped-operand` and `stale-skipped-operand` warnings of `findings`, the findings of
/// `prepared`'s definition loaded on the `native-rust` route, in a fixed order.
pub(super) fn warnings(
    prepared: &PreparedDefinition,
    findings: &[SkippedOperand],
) -> Vec<Diagnostic> {
    let definition = prepared.lowered.definition();
    let keys = keys(prepared);
    let equation_items = equation_items(prepared);
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
        let keyable = match (&function, sentence) {
            (Some(_), Some(sentence))
                if equation_items.iter().any(|item| names_item(sentence, item)) =>
            {
                Keyable::Equation
            }
            (Some(_), _) => Keyable::Function,
            (None, Some(sentence)) if sentence.kind() == krs_ir::SentenceKind::Transition => {
                Keyable::Rule
            }
            _ => Keyable::None,
        };
        // An operator in the prelude is no node of the sentence: it is reported at the
        // sentence's application of the prelude function that holds it.
        let prelude = matches!(finding.through, Some(Through::Builtin { .. }));
        let located = sentence
            .filter(|_| !prelude)
            .and_then(|sentence| locate(&index, sentence, finding));
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
        // A key silences what would be warned: a finding dropped above leaves nothing for it to
        // silence, so a key whose findings are all dropped is stale.
        if silenced(&keys, function.as_deref(), sentence) {
            continue;
        }
        let applied = match (&finding.through, sentence) {
            (Some(Through::Builtin { applied, .. }), Some(sentence)) => {
                applied_at(sentence, applied, finding.occurrence)
            }
            _ => None,
        };
        let warning = render(finding, located.as_ref(), applied, keyable);
        // Two findings the analysis tells apart by their KORE operand (an operator k-rust's
        // chain reaches through two functions, say) can locate at one place, where the author
        // sees one warning.
        let identity = format!("{:?}{}", warning.primary.location, warning.message);
        if seen.insert(identity) {
            warnings.push(warning);
        }
    }
    for key in &keys {
        if !key.used.get() {
            let mut warning = Diagnostic::error(
                codes::analysis::STALE_SKIPPED_OPERAND,
                "`skipped_operand` states that a value may depend on an operand `&&`, `||` or `kequal::ite` skips, but no sentence of this item has a `krs::analysis::skipped-operand` warning to silence",
                key.location.clone(),
            )
            .with_help("remove `skipped_operand`");
            warning.severity = Severity::Warning;
            warnings.push(warning);
        }
    }
    warnings
}

/// Every `skipped_operand` key of `prepared`'s definition: each on a function's production, then
/// each on a rule's or an equation's descriptor.
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
    // A rule's or an equation's key is read from its descriptor: lowering keeps no Semantic IR
    // trace of it, since it states nothing about the sentence's meaning.
    for descriptor in prepared.bundle.descriptors() {
        let skipped = match descriptor.payload() {
            krs_ir::DescriptorPayload::StructuredRule(rule) => rule.skipped_operand.as_ref(),
            krs_ir::DescriptorPayload::HeadRule(rule) => rule.skipped_operand.as_ref(),
            krs_ir::DescriptorPayload::ConfigurationRule(rule) => rule.skipped_operand.as_ref(),
            _ => None,
        };
        if let Some(skipped) = skipped {
            keys.push(Key {
                location: location(
                    descriptor
                        .provenance()
                        .origin_for(&skipped.key)
                        .and_then(krs_ir::OriginStack::exact_authored_range),
                ),
                target: Target::Item(descriptor.id().clone()),
                used: Cell::new(false),
            });
        }
    }
    keys
}

/// Whether a key of `keys` silences a finding anchored at `sentence`, an equation of `function`
/// when that is `Some`, marking each key that does used.
fn silenced(keys: &[Key], function: Option<&str>, sentence: Option<&RuleSentence>) -> bool {
    let mut silenced = false;
    for key in keys {
        let applies = match &key.target {
            Target::Function(symbol) => function == Some(symbol.as_str()),
            Target::Item(item) => sentence.is_some_and(|sentence| names_item(sentence, item)),
        };
        if applies {
            key.used.set(true);
            silenced = true;
        }
    }
    silenced
}

/// Whether `sentence`'s origin names `item`: the item a frame of its transformation into the
/// Semantic IR or the Definition IR records.
fn names_item(sentence: &RuleSentence, item: &krs_ir::StableItemId) -> bool {
    sentence.origin().origin().frames().iter().any(|frame| {
        matches!(
            frame,
            krs_ir::OriginFrame::Transformation { item: Some(named), .. } if named == item
        )
    })
}

/// The items of `prepared`'s definition the author wrote as an equation of a function (an
/// `#[k::equation]` fn, a `k::equations!` row), which take a key of their own: each equation
/// item that a macro invocation other than a function's marker writes, since a function
/// shorthand's marker writes its function and the equations of its body, which its key covers.
fn equation_items(prepared: &PreparedDefinition) -> Vec<krs_ir::StableItemId> {
    let functions = prepared
        .semantic
        .modules()
        .iter()
        .flat_map(krs_ir_levels::SemanticModule::productions)
        .filter_map(|production| macro_invocation(production.origin().origin()).cloned())
        .collect::<Vec<_>>();
    prepared
        .bundle
        .descriptors()
        .iter()
        .filter(|descriptor| match descriptor.payload() {
            krs_ir::DescriptorPayload::StructuredRule(rule)
                if rule.sentence_kind == krs_ir::SentenceKind::Equation =>
            {
                descriptor
                    .provenance()
                    .origin_for(&rule.pattern_key)
                    .and_then(macro_invocation)
                    .is_some_and(|invocation| !functions.contains(invocation))
            }
            _ => false,
        })
        .map(|descriptor| descriptor.id().clone())
        .collect()
}

/// The range of the macro invocation that wrote a node with `origin`.
fn macro_invocation(origin: &krs_ir::OriginStack) -> Option<&SourceRange> {
    origin.frames().iter().find_map(|frame| match frame {
        krs_ir::OriginFrame::Ranged {
            kind: krs_ir::RangedOriginKind::MacroInvocation,
            range,
            ..
        } => Some(range),
        _ => None,
    })
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
/// the finding's operator hook, in the order the analysis walks the emitted sentence's places
/// ([`sentence_nodes`]), the one at the finding's occurrence, which counts every application of
/// the operator as this order does. The analysis walks the emitted K, so where the two orders
/// part (a node KRS rewrote, say), the application at the occurrence is taken where its skipped
/// operand applies the finding's term, else the first whose skipped operand does, else the one
/// at the occurrence.
fn locate(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    sentence: &RuleSentence,
    finding: &SkippedOperand,
) -> Option<Located> {
    let mut candidates = Vec::new();
    for node in sentence_nodes(sentence) {
        if let DefinitionTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } = node.kind()
            && operation.spec().k_hook == Some(finding.operator_hook.as_str())
        {
            candidates.push((node, arguments));
        }
    }
    let term = |(_, arguments): &(&DefinitionTerm, &Vec<DefinitionTerm>)| {
        arguments
            .get(finding.position)
            .and_then(|operand| term_range(index, operand, finding))
    };
    let chosen = candidates
        .get(finding.occurrence)
        .filter(|candidate| term(candidate).is_some())
        .or_else(|| {
            candidates
                .iter()
                .find(|candidate| term(candidate).is_some())
        })
        .or_else(|| candidates.get(finding.occurrence))?;
    let (node, arguments) = chosen;
    let range = node.origin().origin().exact_authored_range()?;
    let operand = arguments.get(finding.position);
    let mut operand_ranges = Vec::new();
    if let Some(operand) = operand {
        preorder(operand, &mut |part| {
            operand_ranges.extend(part.origin().origin().exact_authored_range());
        });
    }
    let first = arguments
        .first()
        .and_then(|first| first.origin().origin().exact_authored_range());
    Some(Located {
        term: term(chosen)
            .and_then(|term| term.range)
            .or_else(|| operand.and_then(value_range)),
        operand_ranges,
        notation: first.is_some_and(|first| first.start_byte < range.start_byte),
        inserted: node.origin().origin().inserted().is_some(),
        node: range,
    })
}

/// The first application in `term` (in preorder) that is the finding's term (module
/// documentation of [`krs_exec::skipped_operand`]), given as its exact authored range, which a
/// node KRS rewrote may lack; `None` when `term` holds no such application. A local function's
/// term is the `let` block or `k::matches!` test the author wrote, whose range is that of the
/// application in its value that may have no value, else its value's.
fn term_range(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    term: &DefinitionTerm,
    finding: &SkippedOperand,
) -> Option<TermNode> {
    if finding.term_local {
        let mut found = None;
        preorder(term, &mut |node| {
            if found.is_none()
                && matches!(
                    node.kind(),
                    DefinitionTermKind::Let { .. } | DefinitionTermKind::Matches { .. }
                )
            {
                found = Some(node);
            }
        });
        let block = found?;
        let inner = finding
            .value_term
            .as_ref()
            .and_then(|head| application_of(index, block_value(block), head));
        return Some(TermNode {
            range: inner.map_or_else(|| value_range(block), |inner| inner.range),
        });
    }
    application_of(
        index,
        term,
        &TermHead {
            symbol: finding.term_symbol.clone(),
            hook: finding.term_hook.clone(),
            arguments: finding.term_arguments.clone(),
        },
    )
}

/// The first application in `term` (in preorder) of `head`'s symbol whose arguments that are
/// applications or literals have `head`'s argument heads.
fn application_of(
    index: &krs_ir_levels::k_surface::DefinitionIndex<'_>,
    term: &DefinitionTerm,
    head: &TermHead,
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
                is_symbol(index, application, &head.symbol, head.hook.as_deref()),
                arguments.iter().collect(),
            ),
            // A collection operation is a term of its own kind, named by its hook.
            DefinitionTermKind::Map(operands) => (
                operands.operation().spec().k_hook == head.hook.as_deref(),
                operands.operands().collect(),
            ),
            DefinitionTermKind::List(operands) => (
                operands.operation().spec().k_hook == head.hook.as_deref(),
                operands.operands().collect(),
            ),
            DefinitionTermKind::Set(operands) => (
                operands.operation().spec().k_hook == head.hook.as_deref(),
                operands.operands().collect(),
            ),
            _ => (false, Vec::new()),
        };
        if matches
            && arguments
                .iter()
                .zip(&head.arguments)
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

/// The authored range of the application in `sentence` of the builtin operation with the K
/// label `label` that is the `occurrence`th in the order the analysis walks the emitted
/// sentence's places ([`sentence_nodes`]), else of the first.
fn applied_at(sentence: &RuleSentence, label: &str, occurrence: usize) -> Option<SourceRange> {
    let found = sentence_nodes(sentence)
        .into_iter()
        .filter(|node| {
            matches!(
                node.kind(),
                DefinitionTermKind::Application {
                    application: ApplicationRef::Builtin(operation),
                    ..
                } if operation.spec().k_label == label
            )
        })
        .map(|node| node.origin().origin().exact_authored_range())
        .collect::<Vec<_>>();
    found
        .get(occurrence)
        .or_else(|| found.first())
        .cloned()
        .flatten()
}

/// The expression that gives a `let` block its value: its body, below every binding; a
/// `k::matches!` test is its own.
fn block_value(term: &DefinitionTerm) -> &DefinitionTerm {
    match term.kind() {
        DefinitionTermKind::Let { body, .. } => block_value(body),
        _ => term,
    }
}

/// The range of the expression that gives `term` its value: a `let` block's body (its final
/// expression, below every binding), else the term's own exact authored range.
fn value_range(term: &DefinitionTerm) -> Option<SourceRange> {
    block_value(term).origin().origin().exact_authored_range()
}

/// An application of a finding's term in its skipped operand ([`term_range`]).
struct TermNode {
    /// Its exact authored range, which a node KRS rewrote may lack.
    range: Option<SourceRange>,
}

/// The nodes of a rule sentence in the order the analysis walks the places of its emitted
/// sentence ([`k_rust::k_rust_backend::short_circuit::ShortCircuitAnalysis::axiom_visits`]):
/// its `requires` conditions, its left-hand side and its function context's cells, its
/// right-hand side, then its `ensures` conditions (a configuration rule's cells hold both sides,
/// in cell order), each in post-order. A condition's top-level conjunctions (`&&`, `bool::and`),
/// which the analysis reads through, are none of them: a conjunct is walked as a condition of
/// its own, and so is the value of a `let` block that stands as one.
fn sentence_nodes(sentence: &RuleSentence) -> Vec<&DefinitionTerm> {
    let mut nodes = Vec::new();
    if let Some(condition) = sentence.requires() {
        for term in condition.terms() {
            condition_nodes(term, &mut nodes);
        }
    }
    let mut terms = Vec::new();
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
    for term in terms {
        postorder(term, &mut |node| nodes.push(node));
    }
    nodes
}

/// The nodes of the condition term `term` in the analysis's order ([`sentence_nodes`]).
fn condition_nodes<'t>(term: &'t DefinitionTerm, nodes: &mut Vec<&'t DefinitionTerm>) {
    match term.kind() {
        DefinitionTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } if matches!(operation.spec().k_hook, Some("BOOL.and" | "BOOL.andThen")) => {
            for argument in arguments {
                condition_nodes(argument, nodes);
            }
        }
        // A `let` block is a local function the condition applies, whose value stands where
        // the block does.
        DefinitionTermKind::Let {
            pattern,
            value,
            body,
            ..
        } => {
            postorder(pattern, &mut |node| nodes.push(node));
            postorder(value, &mut |node| nodes.push(node));
            condition_nodes(body, nodes);
            nodes.push(term);
        }
        _ => postorder(term, &mut |node| nodes.push(node)),
    }
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

/// The note that says where the operator of a finding through another sentence is.
fn through_note(through: Option<&Through>) -> Option<String> {
    let note = match through? {
        Through::Local { .. } => "the operator is in a local function k-rust generates from this sentence's `let` block or `k::matches!` test, which the sentence applies where the block stands".to_owned(),
        Through::Generated { pass } => {
            format!("the operator is in a sentence k-rust's `{pass}` pass generated from this one")
        }
        Through::Builtin {
            module,
            function,
            applied,
        } if applied != function => format!(
            "the operator is in the prelude's `{function}` (module `{module}`), on which the prelude's `{applied}` that this sentence applies depends, and which a definition does not rewrite"
        ),
        Through::Builtin {
            module, function, ..
        } => format!(
            "the operator is in the prelude's `{function}` (module `{module}`), which this sentence applies, and which a definition does not rewrite"
        ),
    };
    Some(note)
}

/// The warning of one finding.
fn render(
    finding: &SkippedOperand,
    located: Option<&Located>,
    applied: Option<SourceRange>,
    keyable: Keyable,
) -> Diagnostic {
    let function = matches!(keyable, Keyable::Function | Keyable::Equation);
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
    if let Some(note) = through_note(finding.through.as_ref()) {
        warning = warning.with_note(note);
    }
    let or = if prelude { "" } else { "or " };
    let key = |marker: &str| format!("`#[k::{marker}(.., skipped_operand = \"..\")]`");
    let keyed = match keyable {
        Keyable::Function => Some(key("function")),
        Keyable::Equation => Some(format!(
            "{} on this equation, or {} on its function, for every equation of the function",
            key("equation"),
            key("function")
        )),
        Keyable::Rule => Some(key("rule")),
        Keyable::None => None,
    };
    if let Some(keyed) = keyed {
        warning = warning.with_help(format!(
            "{or}state that the strict meaning is intended: {keyed}"
        ));
    } else if finding.anchor.is_some() {
        let or = if prelude { "" } else { "or, " };
        warning = warning.with_help(format!(
            "{or}to state that the strict meaning is intended, move the expression into a function, which takes `#[k::function(.., skipped_operand = \"..\")]`"
        ));
    }
    warning
}
