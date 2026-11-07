//! Guard families: the sentences KRS's admission compares with one another,
//! the atoms of their guards, and the flips of an atom that keep the
//! sentences apart.
//!
//! A family is a set of sentences that the admission checks keep pairwise
//! disjoint. Transitions form families through the overlap check's own pairs
//! ([`Siblings`]): the transitions at one priority whose patterns unify,
//! closed transitively. Equations form one family per function instance and
//! rank, the equations the overlap check of equations compares
//! ([`equation_families`]); `owise` equations are a rank of their own.
//!
//! An atom is a maximal `Bool` subterm of a guard that is not a Boolean
//! connective (negation, conjunction, disjunction, implication, `==Bool` and
//! its negations): connectives at any depth are flattened, so the negated
//! copies of an `if` condition in later branches are occurrences of that
//! condition. Two occurrences are one atom when they render one authored
//! construct (one exact authored range), or when they lie in two sentences
//! of a pair and are one term, or complements, under the pair's unifier
//! ([`Unification::relate`], the comparison the overlap check's
//! complementary-conjunct test makes). A comparison and its complement are
//! one atom with opposite polarity. A `k::matches!` test that binds nothing
//! is an atom like any other: its negation is a guard an author can write.
//! Nodes KRS inserted, `k::matches!` tests that bind a local (negated, the
//! local would be bound by nothing) and `let` blocks stay in the abstraction
//! as atoms nothing flips, and the conjuncts of a `k::bits!` template are no
//! Boolean atoms at all.
//!
//! Each guard is a propositional formula over the family's atoms. A flip of
//! atom `α` on a set `S` of sentences replaces `α` by `¬α` in each guard of
//! `S`. Substituting a negated variable is a bijection on valuations, so
//! when every two sentences of the family whose patterns unify have guards
//! that no valuation satisfies together (with the atoms as free variables),
//! a flip that changes no pair across the boundary of `S` keeps that true
//! under every interpretation of the atoms, so the flipped family is still
//! pairwise disjoint. The sets that qualify and are minimal are the
//! connected components of the graph that links two sentences mentioning
//! `α` when flipping one of them alone lets them overlap; each component, of
//! any size, is one obligation, and the flip of every sentence mentioning
//! `α` is the union of its components. A family of one guarded sentence has
//! no pair to keep apart, so each of its atoms is one obligation on that
//! sentence: a corpus that cannot tell `α` from `¬α` there does not observe
//! the atom.
//!
//! A `k::bits!` template in a guard is read from its shape and from what it
//! renders: on one binder, a lower bound `x >= 0`, an upper bound `x < 2^w`
//! and the equalities of fixed runs `bitRange(x, i, n) == c`, each a
//! comparison that renders no comparison of its own in the source. The
//! desugaring gives every token of a sentence's template guards one span
//! (the first token of the authored condition, which other templates and
//! that first authored node share), so a rendered comparison has the range
//! of its operands; an authored comparison's range strictly contains each
//! operand's, since the operator lies between them. A range alone names no
//! template, but this distinguishes a template from the same bounds written
//! out, which are authored atoms an author can negate and are flipped, or
//! reported, as every other atom is. Bit atoms are
//! the bits of an `Int` argument of an equation family whose binder some
//! equation's guard holds a template with a fixed run on. Each equation's bit
//! condition on that argument (its template, its literal pattern, or its
//! `x =/=Int c` holes) is a set of values, evaluated by [`holding_values`];
//! flipping bit `k` is `x ↦ x ⊕ 2^k` on the sets of the flipped equations,
//! a bijection of the argument's values, so the same component construction
//! applies with the set intersection in place of the propositional test.
//! Every such argument has its own bit atoms, and two sentences overlap only
//! where every argument's sets meet and the formulas are satisfiable
//! together.
//!
//! A candidate whose sentences take part in a pair that the abstraction
//! cannot separate (a pair kept apart by literals in patterns, or by
//! comparisons that are no complements) is not generated: nothing then
//! guarantees the flipped family stays disjoint. Nor are flips of a `nondet`
//! group's members (they overlap by design), of claim helpers (sentences of
//! a spec module), of a family whose atom identity is not one relation, of
//! an authored atom some node states that a flip cannot edit, or of the bits of an
//! argument whose values are no one evaluable domain. Each is reported with
//! its reason. The abstraction is a sufficient condition: KRS's judge of the
//! edit stays the authority on whether the flipped definition is admitted.

use std::collections::{BTreeMap, BTreeSet};

use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, GuardMeaning, PackageId, SemanticId,
    SourceMapKey, SourceRange, StableItemId,
};
use krs_ir_levels::{
    IrCondition, SemanticModule, SemanticRule, SemanticRuleCondition, SemanticSortRef,
    SemanticTerm, SemanticTermKind,
};

use crate::equation_domain::{POINT_LIMIT, ValueQuery, equation_families, holding_values};
use crate::overlap::{AtomRelation, Siblings, Side, Unification, guard_conjuncts};

/// One family of sentences KRS's admission keeps pairwise disjoint, with
/// its atoms, its flip obligations, and the flips it does not generate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardFamily {
    /// What kind of sentences the family holds.
    pub kind: FamilyKind,
    /// The sentences, in stable-identity order.
    pub sentences: Vec<FamilySentence>,
    /// The atoms a flip may change: the flippable Boolean atoms in order of
    /// first occurrence, then the bit atoms by argument and bit.
    pub atoms: Vec<GuardAtom>,
    /// The flips that keep the family disjoint by the propositional
    /// argument, one per minimal closed set of sentences.
    pub obligations: Vec<Flip>,
    /// The flips not generated, each with its reason.
    pub not_generated: Vec<NotGenerated>,
}

/// What kind of sentences a family holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FamilyKind {
    /// Transitions at one priority.
    Rules {
        /// The priority, 50 by default.
        priority: u32,
    },
    /// Equations of one function at one rank.
    Equations {
        /// The function.
        function: StableItemId,
        /// The written priority, 50 by default; `None` for the `owise`
        /// equations.
        priority: Option<u32>,
    },
}

/// One sentence of a family.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FamilySentence {
    /// The sentence's stable identity.
    pub rule: StableItemId,
    /// The sentence's source-map key ([`crate::rule_sentence_key`]).
    pub key: SourceMapKey,
}

/// An atom of a family's guards.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GuardAtom {
    /// What the atom is.
    pub kind: AtomKind,
    /// Every node a flip of the atom edits, in sentence order.
    pub occurrences: Vec<AtomOccurrence>,
}

/// What an atom is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AtomKind {
    /// A Boolean atom of the guards.
    Boolean {
        /// The head of the atom's first occurrence: the first declared
        /// production it applies, else its builtin operation.
        head: String,
    },
    /// Bit `bit` of argument `column` (zero-based) of the family's function.
    Bit {
        /// The argument.
        column: usize,
        /// The bit, the least significant being 0.
        bit: u32,
    },
}

/// One node a flip edits.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AtomOccurrence {
    /// The sentence, as an index into [`GuardFamily::sentences`].
    pub sentence: usize,
    /// The node's semantic source-map key.
    pub key: SourceMapKey,
    /// The node's exact authored range.
    pub range: Option<SourceRange>,
    /// For a Boolean atom, whether the node states the atom (`false`: its
    /// complement); for a bit atom, the bit's value in the constant the node
    /// holds (a template's fixed run, a literal, a hole's literal).
    pub positive: bool,
}

/// One flip obligation: atom `atom` flipped in `sentences`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Flip {
    /// A deterministic presentation identity, unique among all families:
    /// `<operator>--<edited sentences>--<atom head>[-n]`.
    pub id: String,
    /// What the flip edits.
    pub operator: FlipOperator,
    /// The atom, as an index into [`GuardFamily::atoms`].
    pub atom: usize,
    /// The flipped sentences, as indices into [`GuardFamily::sentences`].
    pub sentences: Vec<usize>,
    /// Whether the set is every sentence that mentions the atom.
    pub whole: bool,
}

/// What a flip edits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FlipOperator {
    /// A Boolean atom, negated in every occurrence.
    Flip,
    /// A bit, toggled in every constant that fixes it.
    BitFlip,
}

impl FlipOperator {
    /// The operator's stable spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Flip => "flip",
            Self::BitFlip => "bitflip",
        }
    }
}

/// A flip, or a family's flips, not generated.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NotGenerated {
    /// Why.
    pub reason: NotGeneratedReason,
    /// The atom, when one is concerned, as an index into
    /// [`GuardFamily::atoms`].
    pub atom: Option<usize>,
    /// The sentences concerned, as indices into [`GuardFamily::sentences`].
    pub sentences: Vec<usize>,
    /// The pair the reason names, when there is one.
    pub pair: Option<[usize; 2]>,
    /// What the reason is about, in words.
    pub detail: String,
}

/// Why a flip is not generated.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NotGeneratedReason {
    /// A pair the flip involves is kept apart only by theory (literals in
    /// patterns, comparisons that are no complements), so nothing
    /// guarantees the flipped pair stays apart.
    TheorySeparated,
    /// The sentences are members of a `nondet` group, which overlap by
    /// design.
    NondetGroup,
    /// The sentences are claim helpers (sentences of a spec module).
    ClaimHelper,
    /// The identity of an atom is not one relation: a construct renders
    /// several atoms, or two relations (one construct, a pair's unifier)
    /// disagree on whether two occurrences are one atom.
    AtomIdentity,
    /// An occurrence of an authored atom is a node a flip cannot edit: a
    /// node KRS inserted, a `k::matches!` test that binds a local, a `let`
    /// block, or a node without an exact authored range. An atom only KRS's
    /// inserted nodes state is no guard the author wrote, and gets no row.
    Unflippable,
    /// The fixed bits of a `k::bits!` template are no bit atoms: the
    /// template is not on an `Int` argument of an equation (a rule's
    /// pattern, a nested position), or the templates of one argument differ
    /// in width.
    BitDomain,
    /// A bit argument's value sets are beyond the bounded evaluation: its
    /// `2^w` values exceed [`POINT_LIMIT`], or a condition cannot be decided
    /// at one of them.
    EvaluationBound,
}

impl NotGeneratedReason {
    /// The reason's stable spelling.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TheorySeparated => "theory-separated",
            Self::NondetGroup => "nondet-group",
            Self::ClaimHelper => "claim-helper",
            Self::AtomIdentity => "atom-identity",
            Self::Unflippable => "unflippable",
            Self::BitDomain => "bit-domain",
            Self::EvaluationBound => "evaluation-bound",
        }
    }
}

/// The guard families of `modules` (the pre-derivation theory,
/// [`crate::RetainedLowering::pre_derivation`]) that have a guard or a bit
/// argument, ordered by their first sentence's identity, each with its
/// atoms, obligations and flips not generated.
#[must_use]
pub fn guard_families(modules: &[SemanticModule]) -> Vec<GuardFamily> {
    let siblings = Siblings::of(modules);
    let spec = modules
        .iter()
        .filter(|module| module.is_spec())
        .flat_map(SemanticModule::rules)
        .map(SemanticRule::id)
        .collect::<BTreeSet<_>>();
    let mut families = Vec::new();
    let pairs = siblings.pairs();
    for family in siblings.families(&pairs) {
        let members = family
            .rules
            .iter()
            .map(|rule| Member {
                rule: rule.rule,
                group: rule.group,
                guard: rule.guard,
            })
            .collect::<Vec<_>>();
        let position = position_of(&members);
        let mut joined = BTreeMap::<(usize, usize), Vec<&Unification<'_, '_>>>::new();
        for pair in pairs.iter().filter(|pair| !pair.unifications.is_empty()) {
            if let (Some(&left), Some(&right)) = (
                position.get(pair.rules[0].id()),
                position.get(pair.rules[1].id()),
            ) {
                joined
                    .entry((left, right))
                    .or_default()
                    .extend(&pair.unifications);
            }
        }
        let pairs = joined
            .into_iter()
            .map(|((left, right), unifications)| Pair {
                sentences: [left, right],
                unifications,
            })
            .collect::<Vec<_>>();
        let conjuncts = conjuncts_of(&members);
        // A transition has no argument, so its templates hold no bit atoms.
        let bits = bit_arguments(modules, &members, &[], &conjuncts);
        let input = Input {
            kind: FamilyKind::Rules {
                priority: family.priority,
            },
            members: &members,
            pairs: &pairs,
            spec: &spec,
            conjuncts: &conjuncts,
        };
        families.extend(analyze(&siblings, &input, bits));
    }
    for family in equation_families(modules) {
        families.extend(equation_family(&siblings, modules, &family, &spec));
    }
    families.sort_by(|left, right| left.sentences[0].rule.cmp(&right.sentences[0].rule));
    assign_identities(&mut families);
    families
}

/// The guard family of one equation family, when it has a guard.
fn equation_family<'m>(
    siblings: &Siblings<'m>,
    modules: &'m [SemanticModule],
    family: &crate::equation_domain::EquationFamily<'m>,
    spec: &BTreeSet<&'m StableItemId>,
) -> Option<GuardFamily> {
    // A family without a guard has no atom and no template.
    if family.rules.iter().all(|rule| bool_guard(rule).is_none()) {
        return None;
    }
    let members = family
        .rules
        .iter()
        .map(|&rule| Member {
            rule,
            group: None,
            guard: bool_guard(rule),
        })
        .collect::<Vec<_>>();
    let conjuncts = conjuncts_of(&members);
    let bits = bit_arguments(modules, &members, &family.columns, &conjuncts);
    // The bit arguments' literals are read as value sets, so a pair is one
    // whatever its literals there.
    let any_literal = bits
        .columns
        .iter()
        .map(|column| column.column)
        .collect::<Vec<_>>();
    let mut owned = Vec::new();
    for (left, &first) in family.rules.iter().enumerate() {
        for (offset, &second) in family.rules[left + 1..].iter().enumerate() {
            let unifications = siblings.equation_unifications(first, second, &any_literal);
            if !unifications.is_empty() {
                owned.push(([left, left + 1 + offset], unifications));
            }
        }
    }
    let pairs = owned
        .iter()
        .map(|(sentences, unifications)| Pair {
            sentences: *sentences,
            unifications: unifications.iter().collect(),
        })
        .collect::<Vec<_>>();
    let input = Input {
        kind: FamilyKind::Equations {
            function: family.production.id().clone(),
            priority: (family.rank != crate::equation_domain::OWISE_EQUATION_RANK)
                .then_some(family.rank),
        },
        members: &members,
        pairs: &pairs,
        spec,
        conjuncts: &conjuncts,
    };
    analyze(siblings, &input, bits)
}

/// One sentence of a family under analysis.
struct Member<'m> {
    rule: &'m SemanticRule,
    group: Option<(&'m PackageId, &'m str)>,
    guard: Option<&'m SemanticTerm>,
}

/// Two sentences of a family whose patterns unify, with every unification.
struct Pair<'u, 'g, 'm> {
    sentences: [usize; 2],
    unifications: Vec<&'u Unification<'g, 'm>>,
}

/// What [`analyze`] reads of one family.
struct Input<'a, 'u, 'g, 'm> {
    kind: FamilyKind,
    members: &'a [Member<'m>],
    pairs: &'a [Pair<'u, 'g, 'm>],
    spec: &'a BTreeSet<&'m StableItemId>,
    /// Each sentence's guard conjuncts ([`guard_conjuncts`]).
    conjuncts: &'a [Vec<&'m SemanticTerm>],
}

fn conjuncts_of<'m>(members: &[Member<'m>]) -> Vec<Vec<&'m SemanticTerm>> {
    members
        .iter()
        .map(|member| member.guard.map(guard_conjuncts).unwrap_or_default())
        .collect()
}

fn position_of<'m>(members: &[Member<'m>]) -> BTreeMap<&'m StableItemId, usize> {
    members
        .iter()
        .enumerate()
        .map(|(position, member)| (member.rule.id(), position))
        .collect()
}

fn bool_guard(rule: &SemanticRule) -> Option<&SemanticTerm> {
    rule.requires()
        .and_then(IrCondition::as_bool)
        .map(SemanticRuleCondition::term)
}

/// The exact authored range of a node KRS did not insert.
fn authored(term: &SemanticTerm) -> Option<SourceRange> {
    let origin = term.origin().origin();
    if origin.inserted().is_some() {
        return None;
    }
    origin.exact_authored_range()
}

fn int_value(term: &SemanticTerm) -> Option<i128> {
    match (term.kind(), term.sort()) {
        (SemanticTermKind::Token { value }, SemanticSortRef::Builtin(BuiltinSort::Int)) => {
            value.parse().ok()
        }
        _ => None,
    }
}

fn variable(term: &SemanticTerm) -> Option<&SemanticId> {
    match term.kind() {
        SemanticTermKind::Variable { variable } => Some(variable),
        _ => None,
    }
}

/// A relation literal of the catalog ([`GuardMeaning::Relation`]), its
/// operands in the relation's order.
struct Literal<'m> {
    relation: BuiltinOperation,
    positive: bool,
    operands: [&'m SemanticTerm; 2],
}

fn literal(term: &SemanticTerm) -> Option<Literal<'_>> {
    let SemanticTermKind::Application {
        application: ApplicationRef::Builtin(operation),
        arguments,
        ..
    } = term.kind()
    else {
        return None;
    };
    match (operation.guard_meaning(), arguments.as_slice()) {
        (GuardMeaning::Negation, [operand]) => literal(operand).map(|literal| Literal {
            positive: !literal.positive,
            ..literal
        }),
        (GuardMeaning::Relation(meaning), [left, right]) => Some(Literal {
            relation: meaning.relation,
            positive: meaning.positive,
            operands: if meaning.swapped {
                [right, left]
            } else {
                [left, right]
            },
        }),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// `k::bits!` templates

/// A `k::bits!` template in a guard: the conjuncts that bound one binder to
/// `0..2^w` and fix runs of its bits.
struct Template<'m> {
    binder: &'m SemanticId,
    width: u32,
    /// Every conjunct of the template, as indices into the guard's conjuncts.
    conjuncts: Vec<usize>,
    /// The fixed runs: conjunct, offset, length, value.
    runs: Vec<(usize, u32, u32, i128)>,
}

/// One conjunct read as part of a template.
enum TemplatePart<'m> {
    Lower(&'m SemanticId),
    Upper(&'m SemanticId, u32),
    Run(&'m SemanticId, u32, u32, i128),
}

impl<'m> TemplatePart<'m> {
    const fn binder(&self) -> &'m SemanticId {
        match self {
            Self::Lower(binder) | Self::Upper(binder, _) | Self::Run(binder, ..) => binder,
        }
    }
}

fn template_part(term: &SemanticTerm) -> Option<TemplatePart<'_>> {
    let literal = literal(term)?;
    let [left, right] = literal.operands;
    if authored_comparison(term, &literal) {
        return None;
    }
    match (literal.relation, literal.positive) {
        // `x >= 0` is `¬(x < 0)`.
        (BuiltinOperation::IntLess, false) if int_value(right) == Some(0) => {
            Some(TemplatePart::Lower(variable(left)?))
        }
        (BuiltinOperation::IntLess, true) => {
            let bound = u128::try_from(int_value(right)?).ok()?;
            if bound < 2 || !bound.is_power_of_two() {
                return None;
            }
            Some(TemplatePart::Upper(variable(left)?, bound.trailing_zeros()))
        }
        (BuiltinOperation::IntEqual, true) => {
            let (range, value) = match (int_value(left), int_value(right)) {
                (None, Some(value)) => (left, value),
                (Some(value), None) => (right, value),
                _ => return None,
            };
            let SemanticTermKind::Application {
                application: ApplicationRef::Builtin(BuiltinOperation::IntBitRange),
                arguments,
                ..
            } = range.kind()
            else {
                return None;
            };
            let [subject, offset, length] = arguments.as_slice() else {
                return None;
            };
            Some(TemplatePart::Run(
                variable(subject)?,
                u32::try_from(int_value(offset)?).ok()?,
                u32::try_from(int_value(length)?).ok()?,
                value,
            ))
        }
        _ => None,
    }
}

/// Whether a relation literal is a comparison the author wrote: a node KRS
/// did not insert whose exact authored range is none of its operands'
/// ranges. A written comparison's text strictly contains each operand's,
/// the operator lying between them; a `k::bits!` rendering gives every
/// token one span, so it and its operands have one range.
fn authored_comparison(term: &SemanticTerm, literal: &Literal<'_>) -> bool {
    authored(term).is_some_and(|range| {
        literal.operands.iter().all(|operand| {
            operand.origin().origin().exact_authored_range().as_ref() != Some(&range)
        })
    })
}

/// The templates among a guard's conjuncts, one per binder: the conjuncts
/// on that binder that are a lower bound `0`, an upper bound `2^w` and
/// fixed runs, each rendering no comparison of its own
/// ([`authored_comparison`]), when there is a lower bound and every upper
/// bound has one width. Several templates on one binder conjoined are one
/// template, the union of their fixed runs. The same bounds written out
/// (`x >= 0 && x < 256 && ...`) are authored comparisons, so they are
/// Boolean atoms: their negation is an edit of what the author wrote, and
/// reading them as a template would leave it neither generated nor
/// reported.
fn templates<'m>(conjuncts: &[&'m SemanticTerm]) -> Vec<Template<'m>> {
    let mut groups = BTreeMap::<&SemanticId, Vec<(usize, TemplatePart<'m>)>>::new();
    for (index, conjunct) in conjuncts.iter().enumerate() {
        if let Some(part) = template_part(conjunct) {
            groups.entry(part.binder()).or_default().push((index, part));
        }
    }
    let mut found = Vec::new();
    for (binder, parts) in groups {
        let mut lower = false;
        let mut widths = BTreeSet::new();
        let mut runs = Vec::new();
        for (index, part) in &parts {
            match part {
                TemplatePart::Lower(_) => lower = true,
                TemplatePart::Upper(_, width) => {
                    widths.insert(*width);
                }
                TemplatePart::Run(_, offset, length, value) => {
                    runs.push((*index, *offset, *length, *value));
                }
            }
        }
        let widths = widths.into_iter().collect::<Vec<_>>();
        if let (true, &[width]) = (lower, widths.as_slice()) {
            found.push(Template {
                binder,
                width,
                conjuncts: parts.iter().map(|(index, _)| *index).collect(),
                runs,
            });
        }
    }
    found
}

/// A conjunct of a bit argument's binder `x` that the bit abstraction reads:
/// a hole `x =/=Int c` (`Ok(false)`) or a point `x ==Int c` (`Ok(true)`), with
/// its literal.
fn bit_point(term: &SemanticTerm, binder: &SemanticId) -> Option<(bool, i128)> {
    let literal = literal(term)?;
    if literal.relation != BuiltinOperation::IntEqual {
        return None;
    }
    let [left, right] = literal.operands;
    let value = match (variable(left), variable(right)) {
        (Some(name), None) if name == binder => int_value(right)?,
        (None, Some(name)) if name == binder => int_value(left)?,
        _ => return None,
    };
    Some((literal.positive, value))
}

// ---------------------------------------------------------------------------
// Value sets of a bit argument

/// The values of a bit argument at which one equation's bit condition
/// holds: inside `0..2^w` as a table, outside it as a finite set or its
/// complement.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Values {
    inside: Vec<bool>,
    outside: Outside,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Outside {
    Only(BTreeSet<i128>),
    AllBut(BTreeSet<i128>),
}

impl Outside {
    /// The part outside `0..2^w` conjoined with a hole `x =/=Int value`
    /// (`point` false) or a point `x ==Int value` (`point` true); `inside`
    /// says whether `value` lies in `0..2^w`.
    fn with(self, point: bool, value: i128, inside: bool) -> Self {
        match (self, point) {
            // A hole removes its value.
            (Self::Only(mut values), false) => {
                values.remove(&value);
                Self::Only(values)
            }
            (Self::AllBut(mut values), false) => {
                values.insert(value);
                Self::AllBut(values)
            }
            // A point keeps only its value.
            (Self::Only(values), true) => {
                Self::Only(values.into_iter().filter(|kept| *kept == value).collect())
            }
            (Self::AllBut(values), true) => Self::Only(
                (!inside && !values.contains(&value))
                    .then_some(value)
                    .into_iter()
                    .collect(),
            ),
        }
    }

    /// The image under `x ↦ x ⊕ mask`, for a mask below `2^w`, which keeps
    /// the values outside `0..2^w` outside it.
    fn image(&self, mask: usize) -> Self {
        let toggle = |values: &BTreeSet<i128>| {
            values
                .iter()
                .map(|value| value ^ i128::try_from(mask).unwrap_or(0))
                .collect()
        };
        match self {
            Self::Only(values) => Self::Only(toggle(values)),
            Self::AllBut(values) => Self::AllBut(toggle(values)),
        }
    }
}

impl Values {
    fn every(width: u32) -> Self {
        Self {
            inside: vec![true; 1 << width],
            outside: Outside::AllBut(BTreeSet::new()),
        }
    }

    fn inside(&self, value: i128) -> bool {
        usize::try_from(value).is_ok_and(|value| value < self.inside.len())
    }

    /// The set under `x ↦ x ⊕ mask`, for a mask below `2^w`: a bijection
    /// of the integers that keeps `0..2^w` and its complement.
    fn xor(&self, mask: usize) -> Self {
        let mut inside = vec![false; self.inside.len()];
        for (value, holds) in self.inside.iter().enumerate() {
            inside[value ^ mask] = *holds;
        }
        Self {
            inside,
            outside: self.outside.image(mask),
        }
    }

    /// Whether some value is in the image of this set under `x ↦ x ⊕ mask`
    /// and in the image of `other` under `x ↦ x ⊕ other_mask`, both masks
    /// below `2^w`.
    fn meets(&self, mask: usize, other: &Self, other_mask: usize) -> bool {
        if (0..self.inside.len())
            .any(|value| self.inside[value ^ mask] && other.inside[value ^ other_mask])
        {
            return true;
        }
        match (self.outside.image(mask), other.outside.image(other_mask)) {
            (Outside::Only(left), Outside::Only(right)) => !left.is_disjoint(&right),
            (Outside::Only(only), Outside::AllBut(but))
            | (Outside::AllBut(but), Outside::Only(only)) => !only.is_subset(&but),
            // Two cofinite sets of integers always meet.
            (Outside::AllBut(_), Outside::AllBut(_)) => true,
        }
    }
}

/// The bit argument of an equation family: its column, its width, each
/// equation's value set, and the nodes a flip of each bit edits.
struct BitColumn {
    column: usize,
    width: u32,
    values: Vec<Values>,
    /// Per sentence, the nodes holding constants.
    constants: Vec<Vec<Held>>,
}

/// A node holding a constant a bit flip edits: its key, range and constant.
type Held = (SourceMapKey, Option<SourceRange>, Constant);

/// A constant a bit flip edits.
#[derive(Clone, Copy)]
enum Constant {
    /// A template's fixed run: its offset, length and value.
    Run(u32, u32, i128),
    /// A literal pattern, hole or point.
    Literal(i128),
}

impl Constant {
    /// The value of `bit` in the constant, when the constant fixes it.
    fn bit(self, bit: u32) -> Option<bool> {
        match self {
            Self::Run(offset, length, value) => {
                (offset <= bit && bit < offset + length).then(|| (value >> (bit - offset)) & 1 == 1)
            }
            Self::Literal(value) => Some((value >> bit) & 1 == 1),
        }
    }
}

// ---------------------------------------------------------------------------
// The propositional abstraction

/// A guard as a formula over atom occurrences.
#[derive(Clone, Debug)]
enum Formula {
    Constant(bool),
    Occurrence(usize),
    Not(Box<Self>),
    And(Vec<Self>),
    Or(Vec<Self>),
    Iff(Box<Self>, Box<Self>),
}

/// One occurrence of an atom.
struct Occurrence<'m> {
    sentence: usize,
    term: &'m SemanticTerm,
    range: Option<SourceRange>,
    /// Whether a flip may edit it: authored, not inserted, and neither a
    /// `k::matches!` test that binds a local nor a `let` block.
    flippable: bool,
}

fn formula<'m>(
    term: &'m SemanticTerm,
    sentence: usize,
    occurrences: &mut Vec<Occurrence<'m>>,
) -> Formula {
    let boolean = *term.sort() == SemanticSortRef::Builtin(BuiltinSort::Bool);
    match term.kind() {
        SemanticTermKind::Token { value } if boolean => match value.as_str() {
            "true" => return Formula::Constant(true),
            "false" => return Formula::Constant(false),
            _ => {}
        },
        SemanticTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            arguments,
            ..
        } if boolean => {
            let mut operand = |term| Box::new(formula(term, sentence, occurrences));
            match (operation.guard_meaning(), arguments.as_slice()) {
                (GuardMeaning::Negation, [inner]) => return Formula::Not(operand(inner)),
                (GuardMeaning::Conjunction, [left, right]) => {
                    return Formula::And(vec![*operand(left), *operand(right)]);
                }
                (GuardMeaning::Disjunction, [left, right]) => {
                    return Formula::Or(vec![*operand(left), *operand(right)]);
                }
                (GuardMeaning::Implication, [left, right]) => {
                    return Formula::Or(vec![Formula::Not(operand(left)), *operand(right)]);
                }
                (GuardMeaning::Relation(meaning), [left, right])
                    if meaning.relation == BuiltinOperation::BoolEqual =>
                {
                    let iff = Formula::Iff(operand(left), operand(right));
                    return if meaning.positive {
                        iff
                    } else {
                        Formula::Not(Box::new(iff))
                    };
                }
                _ => {}
            }
        }
        _ => {}
    }
    let range = authored(term);
    let flippable = boolean
        && range.is_some()
        && !matches!(
            term.kind(),
            SemanticTermKind::Matches { binds, .. } if !binds.is_empty()
        )
        && !matches!(term.kind(), SemanticTermKind::Let { .. });
    occurrences.push(Occurrence {
        sentence,
        term,
        range,
        flippable,
    });
    Formula::Occurrence(occurrences.len() - 1)
}

/// The atoms of a family: each occurrence's class and its polarity
/// relative to the class.
struct Atoms {
    class: Vec<usize>,
    negated: Vec<bool>,
}

impl Atoms {
    /// The value of `formula` under a partial valuation of the classes, with
    /// class `flipped` negated: `None` while it is undetermined.
    fn value(
        &self,
        formula: &Formula,
        valuation: &BTreeMap<usize, bool>,
        flipped: Option<usize>,
    ) -> Option<bool> {
        match formula {
            Formula::Constant(value) => Some(*value),
            Formula::Occurrence(occurrence) => {
                let class = self.class[*occurrence];
                valuation
                    .get(&class)
                    .map(|value| value ^ self.negated[*occurrence] ^ (flipped == Some(class)))
            }
            Formula::Not(inner) => self.value(inner, valuation, flipped).map(|value| !value),
            Formula::And(parts) => {
                let mut all = Some(true);
                for part in parts {
                    match self.value(part, valuation, flipped) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => all = None,
                    }
                }
                all
            }
            Formula::Or(parts) => {
                let mut any = Some(false);
                for part in parts {
                    match self.value(part, valuation, flipped) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => any = None,
                    }
                }
                any
            }
            Formula::Iff(left, right) => Some(
                self.value(left, valuation, flipped)? == self.value(right, valuation, flipped)?,
            ),
        }
    }

    fn classes(&self, formula: &Formula, output: &mut Vec<usize>) {
        match formula {
            Formula::Constant(_) => {}
            Formula::Occurrence(occurrence) => {
                let class = self.class[*occurrence];
                if !output.contains(&class) {
                    output.push(class);
                }
            }
            Formula::Not(inner) => self.classes(inner, output),
            Formula::And(parts) | Formula::Or(parts) => {
                for part in parts {
                    self.classes(part, output);
                }
            }
            Formula::Iff(left, right) => {
                self.classes(left, output);
                self.classes(right, output);
            }
        }
    }

    /// Whether some valuation of the classes satisfies every formula, each
    /// with its own flipped class.
    fn satisfiable(&self, formulas: &[(&Formula, Option<usize>)]) -> bool {
        let mut classes = Vec::new();
        for (formula, _) in formulas {
            self.classes(formula, &mut classes);
        }
        self.search(formulas, &classes, &mut BTreeMap::new())
    }

    fn search(
        &self,
        formulas: &[(&Formula, Option<usize>)],
        classes: &[usize],
        valuation: &mut BTreeMap<usize, bool>,
    ) -> bool {
        let mut decided = true;
        for (formula, flipped) in formulas {
            match self.value(formula, valuation, *flipped) {
                Some(false) => return false,
                Some(true) => {}
                None => decided = false,
            }
        }
        if decided {
            return true;
        }
        let Some((&next, rest)) = classes.split_first() else {
            return false;
        };
        for value in [false, true] {
            valuation.insert(next, value);
            if self.search(formulas, rest, valuation) {
                valuation.remove(&next);
                return true;
            }
        }
        valuation.remove(&next);
        false
    }
}

/// A union-find of occurrences with the parity of each to its root.
struct Classes {
    parent: Vec<usize>,
    parity: Vec<bool>,
}

impl Classes {
    fn new(size: usize) -> Self {
        Self {
            parent: (0..size).collect(),
            parity: vec![false; size],
        }
    }

    fn find(&mut self, node: usize) -> (usize, bool) {
        let parent = self.parent[node];
        if parent == node {
            return (node, false);
        }
        let (root, parity) = self.find(parent);
        self.parent[node] = root;
        self.parity[node] ^= parity;
        (root, self.parity[node])
    }

    /// Joins two occurrences, complements when `opposite`; `false` when they
    /// are already joined with the other polarity.
    fn join(&mut self, left: usize, right: usize, opposite: bool) -> bool {
        let (left_root, left_parity) = self.find(left);
        let (right_root, right_parity) = self.find(right);
        if left_root == right_root {
            return left_parity ^ right_parity == opposite;
        }
        let (low, high) = (left_root.min(right_root), left_root.max(right_root));
        self.parent[high] = low;
        self.parity[high] = left_parity ^ right_parity ^ opposite;
        true
    }
}

// ---------------------------------------------------------------------------
// The analysis of one family

/// What a candidate flips.
#[derive(Clone, Copy)]
enum Change {
    /// A Boolean atom's class.
    Atom(usize),
    /// A bit of a bit argument: the argument, as an index into
    /// [`Analysis::bits`], and the bit's mask.
    Bit(usize, usize),
}

/// One family under analysis.
struct Analysis<'a, 'u, 'g, 'm> {
    input: &'a Input<'a, 'u, 'g, 'm>,
    formulas: Vec<Formula>,
    atoms: Atoms,
    bits: Vec<BitColumn>,
}

impl Analysis<'_, '_, '_, '_> {
    fn same_group(&self, left: usize, right: usize) -> bool {
        let members = self.input.members;
        members[left].group.is_some() && members[left].group == members[right].group
    }

    /// Whether sentences `left` and `right` can both apply after `change` is
    /// made in the sentences `flipped` holds: every bit argument's value sets
    /// meet, and the formulas are satisfiable together.
    fn overlap(
        &self,
        left: usize,
        right: usize,
        change: Change,
        flipped: &dyn Fn(usize) -> bool,
    ) -> bool {
        let atom = |sentence| match change {
            Change::Atom(class) if flipped(sentence) => Some(class),
            _ => None,
        };
        for (position, bits) in self.bits.iter().enumerate() {
            let mask = |sentence: usize| match change {
                Change::Bit(changed, mask) if changed == position && flipped(sentence) => mask,
                _ => 0,
            };
            if !bits.values[left].meets(mask(left), &bits.values[right], mask(right)) {
                return false;
            }
        }
        self.atoms.satisfiable(&[
            (&self.formulas[left], atom(left)),
            (&self.formulas[right], atom(right)),
        ])
    }

    /// The minimal closed sets of `mentions` under `change`: the connected
    /// components of the graph linking two sentences whose pair overlaps
    /// when one of them alone is changed.
    fn components(&self, mentions: &[usize], change: Change) -> Vec<Vec<usize>> {
        let mut classes = Classes::new(self.input.members.len());
        for pair in self.input.pairs {
            let [left, right] = pair.sentences;
            if !mentions.contains(&left)
                || !mentions.contains(&right)
                || self.same_group(left, right)
            {
                continue;
            }
            if self.overlap(left, right, change, &|sentence| sentence == left)
                || self.overlap(left, right, change, &|sentence| sentence == right)
            {
                classes.join(left, right, false);
            }
        }
        let mut components = BTreeMap::<usize, Vec<usize>>::new();
        for &sentence in mentions {
            components
                .entry(classes.find(sentence).0)
                .or_default()
                .push(sentence);
        }
        components.into_values().collect()
    }

    /// The first pair involving `set` that overlaps once `change` is made in
    /// `set`.
    fn first_overlap(&self, set: &[usize], change: Change) -> Option<[usize; 2]> {
        self.input.pairs.iter().find_map(|pair| {
            let [left, right] = pair.sentences;
            ((set.contains(&left) || set.contains(&right))
                && !self.same_group(left, right)
                && self.overlap(left, right, change, &|sentence| set.contains(&sentence)))
            .then_some(pair.sentences)
        })
    }
}

/// The head of an atom: the first declared production it applies, in
/// preorder, else its builtin operation, else its kind.
fn atom_head(term: &SemanticTerm) -> String {
    fn declared(term: &SemanticTerm) -> Option<String> {
        if let SemanticTermKind::Application {
            application: ApplicationRef::Declared(id),
            ..
        } = term.kind()
        {
            return Some(id.item_name().to_owned());
        }
        if let SemanticTermKind::Application { arguments, .. } = term.kind() {
            return arguments.iter().find_map(declared);
        }
        None
    }
    if let Some(name) = declared(term) {
        return name;
    }
    match term.kind() {
        SemanticTermKind::Application {
            application: ApplicationRef::Builtin(operation),
            ..
        } => format!("{operation:?}"),
        SemanticTermKind::Variable { variable } => variable.as_str().to_owned(),
        SemanticTermKind::Matches { .. } => "matches".to_owned(),
        _ => "atom".to_owned(),
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "The steps of one family's analysis stay in order in one place."
)]
fn analyze(
    siblings: &Siblings<'_>,
    input: &Input<'_, '_, '_, '_>,
    bits: BitArguments,
) -> Option<GuardFamily> {
    let members = input.members;
    let conjuncts = input.conjuncts;
    let sentences = members
        .iter()
        .map(|member| FamilySentence {
            rule: member.rule.id().clone(),
            key: crate::rederivation::sentence_key(member.rule).clone(),
        })
        .collect::<Vec<_>>();
    let all = (0..members.len()).collect::<Vec<_>>();
    let mut family = GuardFamily {
        kind: input.kind.clone(),
        sentences,
        atoms: Vec::new(),
        obligations: Vec::new(),
        not_generated: Vec::new(),
    };
    if members.iter().all(|member| member.guard.is_none()) && bits.columns.is_empty() {
        return None;
    }
    if members
        .iter()
        .any(|member| input.spec.contains(member.rule.id()))
    {
        family.not_generated.push(NotGenerated {
            reason: NotGeneratedReason::ClaimHelper,
            atom: None,
            sentences: all,
            pair: None,
            detail: "the sentences belong to a spec module".to_owned(),
        });
        return Some(family);
    }
    family.not_generated.extend(bits.refused);
    // One row names a group's members; no flip touching them is generated.
    let mut groups = BTreeMap::<(&PackageId, &str), Vec<usize>>::new();
    for (index, member) in members.iter().enumerate() {
        if let Some(group) = member.group {
            groups.entry(group).or_default().push(index);
        }
    }
    for ((_, name), sentences) in groups {
        family.not_generated.push(NotGenerated {
            reason: NotGeneratedReason::NondetGroup,
            atom: None,
            sentences,
            pair: None,
            detail: format!("the members of nondet group `{name}` overlap by design"),
        });
    }

    // The guards as formulas over occurrences; the conjuncts the bit
    // arguments read, and the templates no bit argument holds, are not
    // Boolean atoms.
    let mut occurrences = Vec::new();
    let mut formulas = Vec::new();
    for (sentence, conjuncts) in conjuncts.iter().enumerate() {
        formulas.push(Formula::And(
            conjuncts
                .iter()
                .enumerate()
                .filter(|(index, _)| !bits.excluded[sentence].contains(index))
                .map(|(_, conjunct)| formula(conjunct, sentence, &mut occurrences))
                .collect(),
        ));
    }

    // Constructs that render several different atoms in one sentence are
    // no atom: they join nothing by their range, and nothing flips them.
    let mut by_range = BTreeMap::<SourceRange, Vec<usize>>::new();
    for (index, occurrence) in occurrences.iter().enumerate() {
        if let Some(range) = &occurrence.range {
            by_range.entry(range.clone()).or_default().push(index);
        }
    }
    let mut several = BTreeSet::new();
    for (range, indices) in &by_range {
        let differ = indices.iter().enumerate().any(|(position, &left)| {
            indices[position + 1..].iter().any(|&right| {
                occurrences[left].sentence == occurrences[right].sentence
                    && siblings.relate_within(occurrences[left].term, occurrences[right].term)
                        != AtomRelation::Same
            })
        });
        if differ {
            several.insert(range.clone());
        }
    }
    let mut renders_several = BTreeSet::new();
    for range in &several {
        let indices = &by_range[range];
        for index in indices {
            occurrences[*index].flippable = false;
            renders_several.insert(*index);
        }
        let sentences = indices
            .iter()
            .map(|index| occurrences[*index].sentence)
            .collect::<BTreeSet<_>>();
        family.not_generated.push(NotGenerated {
            reason: NotGeneratedReason::AtomIdentity,
            atom: None,
            sentences: sentences.into_iter().collect(),
            pair: None,
            detail: format!(
                "one construct at bytes {}..{} renders several atoms",
                range.start_byte, range.end_byte
            ),
        });
    }

    // Atom identity: one construct, then one term or complements within a
    // sentence and under each pair's unifiers.
    let mut classes = Classes::new(occurrences.len());
    let mut consistent = true;
    for (range, indices) in &by_range {
        if several.contains(range) {
            continue;
        }
        for window in indices.windows(2) {
            consistent &= classes.join(window[0], window[1], false);
        }
    }
    let mut relations = Vec::new();
    for left in 0..occurrences.len() {
        for right in left + 1..occurrences.len() {
            if occurrences[left].sentence == occurrences[right].sentence {
                relations.push((
                    left,
                    right,
                    siblings.relate_within(occurrences[left].term, occurrences[right].term),
                ));
            }
        }
    }
    for pair in input.pairs {
        let [first, second] = pair.sentences;
        for unification in &pair.unifications {
            for (left, left_occurrence) in occurrences.iter().enumerate() {
                if left_occurrence.sentence != first {
                    continue;
                }
                for (right, right_occurrence) in occurrences.iter().enumerate() {
                    if right_occurrence.sentence == second {
                        relations.push((
                            left,
                            right,
                            unification.relate(
                                (Side::Left, left_occurrence.term),
                                (Side::Right, right_occurrence.term),
                            ),
                        ));
                    }
                }
            }
        }
    }
    for (left, right, relation) in &relations {
        match relation {
            AtomRelation::Same => consistent &= classes.join(*left, *right, false),
            AtomRelation::Complement => consistent &= classes.join(*left, *right, true),
            AtomRelation::Unrelated => {}
        }
    }
    let conflict = relations.iter().find(|(left, right, relation)| {
        let (left_root, left_parity) = classes.find(*left);
        let (right_root, right_parity) = classes.find(*right);
        left_root == right_root
            && *relation
                != if left_parity == right_parity {
                    AtomRelation::Same
                } else {
                    AtomRelation::Complement
                }
    });
    let identified = consistent && conflict.is_none();
    if !identified {
        let sentences = conflict.map_or_else(
            || all.clone(),
            |(left, right, _)| {
                let mut sentences = vec![occurrences[*left].sentence, occurrences[*right].sentence];
                sentences.dedup();
                sentences
            },
        );
        family.not_generated.push(NotGenerated {
            reason: NotGeneratedReason::AtomIdentity,
            atom: None,
            sentences,
            pair: None,
            detail: "two occurrences are one atom by one relation and not by another; no Boolean flip is generated".to_owned(),
        });
        // Without one identity, every occurrence is its own variable: any
        // valuation of the guards' terms is a valuation of those variables,
        // so the formulas still over-approximate where two sentences
        // overlap, which is all the bit flips read.
        classes = Classes::new(occurrences.len());
    }
    let mut class_of_root = BTreeMap::new();
    let mut atoms = Atoms {
        class: Vec::new(),
        negated: Vec::new(),
    };
    for index in 0..occurrences.len() {
        let (root, parity) = classes.find(index);
        let next = class_of_root.len();
        atoms.class.push(*class_of_root.entry(root).or_insert(next));
        atoms.negated.push(parity);
    }
    let analysis = Analysis {
        input,
        formulas,
        atoms,
        bits: bits.columns,
    };

    // Boolean flips, by atom in order of first occurrence.
    for class in (0..class_of_root.len()).filter(|_| identified) {
        let members_of = (0..occurrences.len())
            .filter(|index| analysis.atoms.class[*index] == class)
            .collect::<Vec<_>>();
        let mentions = members_of
            .iter()
            .map(|index| occurrences[*index].sentence)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let first = members_of[0];
        if !members_of.iter().all(|index| occurrences[*index].flippable) {
            // An atom only KRS's inserted nodes state is no guard the author
            // wrote, and a construct that renders several atoms is already
            // reported. Every other atom the author wrote gets its row here,
            // so that no family's guard leaves the obligations unaccounted.
            let authored_atom = members_of
                .iter()
                .any(|index| occurrences[*index].range.is_some());
            if authored_atom
                && !members_of
                    .iter()
                    .any(|index| renders_several.contains(index))
            {
                let head = atom_head(occurrences[first].term);
                let detail = if members_of.iter().any(|index| occurrences[*index].flippable) {
                    format!("atom `{head}` is also stated by a node a flip cannot edit")
                } else {
                    format!(
                        "atom `{head}` is stated only by nodes a flip cannot edit (a `k::matches!` that binds a local, a `let` block, a node KRS inserted)"
                    )
                };
                family.not_generated.push(NotGenerated {
                    reason: NotGeneratedReason::Unflippable,
                    atom: None,
                    sentences: mentions,
                    pair: None,
                    detail,
                });
            }
            continue;
        }
        let atom = family.atoms.len();
        family.atoms.push(GuardAtom {
            kind: AtomKind::Boolean {
                head: atom_head(occurrences[first].term),
            },
            occurrences: members_of
                .iter()
                .map(|index| AtomOccurrence {
                    sentence: occurrences[*index].sentence,
                    key: occurrences[*index].term.origin().key().clone(),
                    range: occurrences[*index].range.clone(),
                    positive: analysis.atoms.negated[*index] == analysis.atoms.negated[first],
                })
                .collect(),
        });
        candidates(
            &analysis,
            &mut family,
            atom,
            &mentions,
            Change::Atom(class),
            FlipOperator::Flip,
        );
    }

    // Bit flips, by argument, then by bit.
    for (position, bits) in analysis.bits.iter().enumerate() {
        for bit in 0..bits.width {
            let mask = 1_usize << bit;
            let mentions = (0..members.len())
                .filter(|sentence| bits.values[*sentence].xor(mask) != bits.values[*sentence])
                .collect::<Vec<_>>();
            if mentions.is_empty() {
                continue;
            }
            let atom = family.atoms.len();
            family.atoms.push(GuardAtom {
                kind: AtomKind::Bit {
                    column: bits.column,
                    bit,
                },
                occurrences: mentions
                    .iter()
                    .flat_map(|sentence| {
                        bits.constants[*sentence].iter().filter_map(
                            move |(key, range, constant)| {
                                Some(AtomOccurrence {
                                    sentence: *sentence,
                                    key: key.clone(),
                                    range: range.clone(),
                                    positive: constant.bit(bit)?,
                                })
                            },
                        )
                    })
                    .collect(),
            });
            candidates(
                &analysis,
                &mut family,
                atom,
                &mentions,
                Change::Bit(position, mask),
                FlipOperator::BitFlip,
            );
        }
    }
    Some(family)
}

/// The obligations of one atom: each minimal closed set of the sentences
/// that mention it, unless the set holds a `nondet` group's member (the
/// family's row for the group names it) or a pair involving it overlaps
/// once flipped.
fn candidates(
    analysis: &Analysis<'_, '_, '_, '_>,
    family: &mut GuardFamily,
    atom: usize,
    mentions: &[usize],
    change: Change,
    operator: FlipOperator,
) {
    let components = analysis.components(mentions, change);
    let whole = components.len() == 1;
    for component in components {
        if component
            .iter()
            .any(|sentence| analysis.input.members[*sentence].group.is_some())
        {
            continue;
        }
        if let Some(pair) = analysis.first_overlap(&component, change) {
            family.not_generated.push(NotGenerated {
                reason: NotGeneratedReason::TheorySeparated,
                atom: Some(atom),
                sentences: component,
                pair: Some(pair),
                detail: "the pair is kept apart by more than complementary atoms".to_owned(),
            });
            continue;
        }
        family.obligations.push(Flip {
            id: String::new(),
            operator,
            atom,
            sentences: component,
            whole,
        });
    }
}

/// The binder an equation's pattern puts at argument `column`: a variable,
/// or the alias of an `x @ p` pattern.
fn column_binder(rule: &SemanticRule, column: usize) -> Option<&SemanticId> {
    let SemanticTermKind::Application { arguments, .. } = rule.body()?.from().kind() else {
        return None;
    };
    match arguments.get(column)?.kind() {
        SemanticTermKind::Variable { variable }
        | SemanticTermKind::As {
            alias: variable, ..
        } => Some(variable),
        _ => None,
    }
}

/// The bit arguments of a family and what the abstraction leaves out for
/// them.
struct BitArguments {
    /// The arguments whose bits are atoms, in argument order.
    columns: Vec<BitColumn>,
    /// Per sentence, the conjuncts no Boolean atom reads: the templates, and
    /// the bit arguments' holes and points.
    excluded: Vec<BTreeSet<usize>>,
    /// The bits not generated, with their reasons.
    refused: Vec<NotGenerated>,
}

/// The bit arguments of a family whose sentences have the argument sorts
/// `columns` (none for transitions): each `Int` argument whose binder some
/// sentence's guard holds a template with a fixed run on. An argument whose
/// templates differ in width, or whose value sets the bounded evaluation
/// cannot give, has no bit atoms and is refused. The conjuncts of every
/// template with a fixed run are no Boolean atoms, whether or not a bit
/// argument holds it: a fixed-bit test has no negation an author writes.
fn bit_arguments<'m>(
    modules: &'m [SemanticModule],
    members: &[Member<'m>],
    columns: &[SemanticSortRef],
    conjuncts: &[Vec<&'m SemanticTerm>],
) -> BitArguments {
    let found = conjuncts
        .iter()
        .map(|conjuncts| templates(conjuncts))
        .collect::<Vec<_>>();
    let mut excluded = vec![BTreeSet::new(); members.len()];
    let mut refused = Vec::new();
    let candidates = candidate_arguments(members, columns, &found, &mut excluded);
    // A template with a fixed run that no candidate argument holds.
    let mut elsewhere = BTreeSet::new();
    for (sentence, templates) in found.iter().enumerate() {
        for template in templates
            .iter()
            .filter(|template| !template.runs.is_empty())
        {
            if !excluded[sentence].contains(&template.conjuncts[0]) {
                excluded[sentence].extend(template.conjuncts.iter().copied());
                elsewhere.insert(sentence);
            }
        }
    }
    if !elsewhere.is_empty() {
        refused.push(NotGenerated {
            reason: NotGeneratedReason::BitDomain,
            atom: None,
            sentences: elsewhere.into_iter().collect(),
            pair: None,
            detail: "a k::bits! template here is not on an Int argument of an equation".to_owned(),
        });
    }

    // Each candidate's value sets, evaluated in one batch.
    let mut queries = Vec::new();
    let mut asked = Vec::new();
    let mut prepared = Vec::new();
    for (column, held) in candidates {
        let argument = match prepare_argument(members, conjuncts, &found, column, &held) {
            Ok(argument) => argument,
            Err(refusal) => {
                refused.push(refusal);
                continue;
            }
        };
        for (sentence, query) in argument.queries {
            asked.push((prepared.len(), sentence));
            queries.push(query);
        }
        prepared.push((argument.column, argument.points));
    }
    let mut undecided = vec![Vec::new(); prepared.len()];
    for ((position, sentence), answer) in asked.into_iter().zip(holding_values(modules, &queries)) {
        match answer {
            Some(inside) => prepared[position].0.values[sentence].inside = inside,
            None => undecided[position].push(sentence),
        }
    }
    let mut columns = Vec::new();
    for ((column, points), undecided) in prepared.into_iter().zip(undecided) {
        if undecided.is_empty() {
            for (sentence, points) in points.into_iter().enumerate() {
                excluded[sentence].extend(points);
            }
            columns.push(column);
        } else {
            refused.push(NotGenerated {
                reason: NotGeneratedReason::EvaluationBound,
                atom: None,
                sentences: undecided,
                pair: None,
                detail: format!(
                    "the bit condition of argument {} cannot be evaluated on its 2^{} values",
                    column.column, column.width
                ),
            });
        }
    }
    BitArguments {
        columns,
        excluded,
        refused,
    }
}

/// The candidate bit arguments: each `Int` argument whose binder some
/// sentence's guard holds a template with a fixed run on, with the index of
/// each sentence's template there. Every template a candidate holds is
/// added to `excluded`.
fn candidate_arguments(
    members: &[Member<'_>],
    columns: &[SemanticSortRef],
    found: &[Vec<Template<'_>>],
    excluded: &mut [BTreeSet<usize>],
) -> Vec<(usize, Vec<Option<usize>>)> {
    let mut candidates = Vec::new();
    for (column, sort) in columns.iter().enumerate() {
        if *sort != SemanticSortRef::Builtin(BuiltinSort::Int) {
            continue;
        }
        let held = members
            .iter()
            .enumerate()
            .map(|(sentence, member)| {
                let binder = column_binder(member.rule, column)?;
                found[sentence]
                    .iter()
                    .position(|template| template.binder == binder)
            })
            .collect::<Vec<_>>();
        let declared = held.iter().enumerate().any(|(sentence, template)| {
            template.is_some_and(|template| !found[sentence][template].runs.is_empty())
        });
        if declared {
            for (sentence, template) in held.iter().enumerate() {
                if let Some(template) = template {
                    excluded[sentence].extend(found[sentence][*template].conjuncts.iter().copied());
                }
            }
            candidates.push((column, held));
        }
    }
    candidates
}

/// One candidate bit argument, its value sets still to be evaluated.
struct PreparedArgument<'m> {
    column: BitColumn,
    /// Per sentence, its holes and points on the argument's binder.
    points: Vec<Vec<usize>>,
    /// The sentences whose value sets inside `0..2^w` are still to be
    /// evaluated, with their queries.
    queries: Vec<(usize, ValueQuery<'m>)>,
}

/// The bit argument at `column`, whose sentences' templates are `held`, read
/// up to the bounded evaluation: refused when its templates differ in width
/// or its `2^w` values exceed [`POINT_LIMIT`].
fn prepare_argument<'m>(
    members: &[Member<'m>],
    conjuncts: &[Vec<&'m SemanticTerm>],
    found: &[Vec<Template<'m>>],
    column: usize,
    held: &[Option<usize>],
) -> Result<PreparedArgument<'m>, NotGenerated> {
    let sentences = (0..members.len())
        .filter(|sentence| held[*sentence].is_some())
        .collect::<Vec<_>>();
    let widths = held
        .iter()
        .enumerate()
        .filter_map(|(sentence, template)| Some(found[sentence][(*template)?].width))
        .collect::<BTreeSet<_>>();
    let [width] = widths.iter().copied().collect::<Vec<_>>()[..] else {
        return Err(NotGenerated {
            reason: NotGeneratedReason::BitDomain,
            atom: None,
            sentences,
            pair: None,
            detail: format!(
                "the templates of argument {column} differ in width ({})",
                widths
                    .iter()
                    .map(u32::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
        });
    };
    if 1_u64
        .checked_shl(width)
        .is_none_or(|count| count > POINT_LIMIT)
    {
        return Err(NotGenerated {
            reason: NotGeneratedReason::EvaluationBound,
            atom: None,
            sentences,
            pair: None,
            detail: format!(
                "argument {column}'s 2^{width} values exceed the evaluation's bound of {POINT_LIMIT}"
            ),
        });
    }
    let mut argument = PreparedArgument {
        column: BitColumn {
            column,
            width,
            values: Vec::new(),
            constants: Vec::new(),
        },
        points: Vec::new(),
        queries: Vec::new(),
    };
    for (sentence, member) in members.iter().enumerate() {
        let condition = bit_condition(
            member.rule,
            column,
            width,
            &conjuncts[sentence],
            &found[sentence],
        );
        argument
            .queries
            .extend(condition.query.map(|query| (sentence, query)));
        argument.column.values.push(condition.values);
        argument.column.constants.push(condition.held);
        argument.points.push(condition.points);
    }
    Ok(argument)
}

/// One equation's bit condition on a bit argument.
struct BitCondition<'m> {
    /// Its value set, with the part inside `0..2^width` still to be
    /// evaluated when there is a query.
    values: Values,
    /// The nodes holding its constants.
    held: Vec<Held>,
    /// The holes and points on the argument's binder, as indices into the
    /// guard's conjuncts.
    points: Vec<usize>,
    query: Option<ValueQuery<'m>>,
}

/// One equation's bit condition on argument `column`, whose templates have
/// width `width`.
fn bit_condition<'m>(
    rule: &'m SemanticRule,
    column: usize,
    width: u32,
    conjuncts: &[&'m SemanticTerm],
    found: &[Template<'m>],
) -> BitCondition<'m> {
    let mut condition = BitCondition {
        values: Values::every(width),
        held: Vec::new(),
        points: Vec::new(),
        query: None,
    };
    let pattern = rule.body().and_then(|body| match body.from().kind() {
        SemanticTermKind::Application { arguments, .. } => arguments.get(column),
        _ => None,
    });
    if let Some(literals) = pattern.and_then(literal_alternatives) {
        let values = &mut condition.values;
        values.inside.fill(false);
        let mut outside = BTreeSet::new();
        for literal in literals {
            let Some(value) = int_value(literal) else {
                continue;
            };
            match usize::try_from(value) {
                Ok(index) if index < values.inside.len() => values.inside[index] = true,
                _ => {
                    outside.insert(value);
                }
            }
            condition.held.push((
                literal.origin().key().clone(),
                authored(literal),
                Constant::Literal(value),
            ));
        }
        values.outside = Outside::Only(outside);
        return condition;
    }
    let Some(binder) = column_binder(rule, column) else {
        return condition;
    };
    let mut read = Vec::new();
    if let Some(template) = found.iter().find(|template| template.binder == binder) {
        read.extend(template.conjuncts.iter().map(|index| conjuncts[*index]));
        for (index, offset, length, value) in &template.runs {
            let conjunct = conjuncts[*index];
            condition.held.push((
                conjunct.origin().key().clone(),
                conjunct.origin().origin().exact_authored_range(),
                Constant::Run(*offset, *length, *value),
            ));
        }
        condition.values.outside = Outside::Only(BTreeSet::new());
    }
    for (index, conjunct) in conjuncts.iter().enumerate() {
        let Some((point, value)) = bit_point(conjunct, binder) else {
            continue;
        };
        condition.points.push(index);
        read.push(conjunct);
        condition.held.push((
            conjunct.origin().key().clone(),
            authored(conjunct),
            Constant::Literal(value),
        ));
        let inside = condition.values.inside(value);
        let previous = std::mem::replace(
            &mut condition.values.outside,
            Outside::AllBut(BTreeSet::new()),
        );
        condition.values.outside = previous.with(point, value, inside);
    }
    condition.query = (!read.is_empty()).then_some(ValueQuery {
        binder,
        conjuncts: read,
        width,
    });
    condition
}

/// The literals of a literal pattern or an or-pattern of `Int` literals.
fn literal_alternatives(pattern: &SemanticTerm) -> Option<Vec<&SemanticTerm>> {
    match pattern.kind() {
        SemanticTermKind::Token { .. } => Some(vec![pattern]),
        SemanticTermKind::Or { alternatives } => {
            let alternatives = alternatives.iter().collect::<Vec<_>>();
            alternatives
                .iter()
                .all(|alternative| int_value(alternative).is_some())
                .then_some(alternatives)
        }
        _ => None,
    }
}

/// Gives every obligation its presentation identity, in family order, a
/// repeated one numbered from `-2`.
fn assign_identities(families: &mut [GuardFamily]) {
    let mut seen = BTreeMap::<String, usize>::new();
    for family in families {
        let names = family
            .sentences
            .iter()
            .map(|sentence| sentence.rule.item_name().to_owned())
            .collect::<Vec<_>>();
        for flip in &mut family.obligations {
            let edited = flip
                .sentences
                .iter()
                .map(|sentence| names[*sentence].as_str())
                .collect::<Vec<_>>();
            let tails = if edited.len() <= 3 {
                edited.join("+")
            } else {
                format!("{}+{}", edited[0], edited.len() - 1)
            };
            let head = match &family.atoms[flip.atom].kind {
                AtomKind::Boolean { head } => head.clone(),
                AtomKind::Bit { bit, .. } => format!("bit{bit}"),
            };
            let base = format!("{}--{tails}--{head}", flip.operator.as_str());
            let count = seen.entry(base.clone()).or_insert(0);
            *count += 1;
            flip.id = if *count == 1 {
                base
            } else {
                format!("{base}-{count}")
            };
        }
    }
}

/// The over-approximation the guard families rely on, checked: every two
/// equations of one [`equation_families`] family that the overlap check of
/// equations finds may both apply have a unification in
/// [`Siblings::equation_unifications`] (read with no relaxed argument, the
/// fewest pairs it gives). The equation check pairs equations its own way,
/// so the guard families may read more pairs than it compares, which only
/// adds constraints to a flip; a pair it compares and they miss would let a
/// flip make two equations overlap that the families never kept apart.
///
/// "May both apply" is the check's own reading. Where the ground analysis
/// enumerates a family, two equations that both hold at an argument point;
/// where it cannot decide (the family is beyond it, or some equation is
/// undecided at a point), also every pair whose argument patterns the
/// coverage unifier does not prove disjoint ([`crate::coverage::heads_may_match`]),
/// the pairs `coverage::overlap` goes on to examine.
///
/// Returns the number of pairs checked and a description of each pair
/// missing from the unifications.
#[cfg(any(test, feature = "test-support"))]
pub(crate) fn equation_pairs_outside_unifications(
    modules: &[SemanticModule],
) -> (usize, Vec<String>) {
    use crate::coverage::{EquationSignature, heads_may_match};
    use crate::equation_domain::{Domain, equation_view};

    let siblings = Siblings::of(modules);
    let signature = EquationSignature::new(modules);
    let evaluator = signature.evaluator(modules);
    let mut checked = 0;
    let mut missing = Vec::new();
    for family in equation_families(modules) {
        let rules = &family.rules;
        if rules.len() < 2 {
            continue;
        }
        let mut applying = BTreeSet::new();
        let mut decided = false;
        let views = rules
            .iter()
            .map(|rule| equation_view(rule))
            .collect::<Option<Vec<_>>>();
        if let Some(domain) = views
            .as_deref()
            .and_then(|views| Domain::new(&evaluator, &family.columns, views))
        {
            decided = true;
            for point in domain.points() {
                let mut here = Vec::new();
                for index in 0..rules.len() {
                    match domain.applies(index, &point) {
                        Ok(true) => here.push(index),
                        Ok(false) => {}
                        Err(_) => decided = false,
                    }
                }
                for (position, &first) in here.iter().enumerate() {
                    applying.extend(here[position + 1..].iter().map(|&second| (first, second)));
                }
            }
        }
        if !decided {
            for first in 0..rules.len() {
                for second in first + 1..rules.len() {
                    if heads_may_match(&signature, rules[first], rules[second]) {
                        applying.insert((first, second));
                    }
                }
            }
        }
        for (first, second) in applying {
            checked += 1;
            if siblings
                .equation_unifications(rules[first], rules[second], &[])
                .is_empty()
            {
                missing.push(format!(
                    "{} and {}, equations of {} at rank {}",
                    rules[first].id(),
                    rules[second].id(),
                    family.production.id(),
                    family.rank
                ));
            }
        }
    }
    (checked, missing)
}

#[cfg(test)]
mod tests;
