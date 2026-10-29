//! `A | B` at the root of an equation's subject.
//!
//! An equation defines one function by matching its arguments, so each
//! alternative of a root `F(a) | F(b)` is a whole application of the function
//! it defines, and the equation is one equation per alternative. An
//! application distributes over `|`, so that root is `F(a | b)`: the
//! alternatives below the function, which is one equation per alternative as
//! well. The root is moved there before anything else reads the bundle, as a
//! constant is inlined, so sort inference, the overlap and coverage checks,
//! and emission read one form, the one written below the root.
//!
//! Distribution is exact where the alternatives differ in one argument at
//! most. An equation matches each argument on its own, so `F(a, b) | F(c, d)`
//! is not `F(a | c, b | d)`, which also matches `F(a, d)`, and alternatives
//! that differ in two arguments are refused. Alternatives that apply no one
//! head are left at the root: an alternative that applies no function is the
//! root's mistake, which only the declaration its head resolves to tells, so
//! the equation's own check (`subject_roots`) reports it, as it does without
//! `|`, and refuses alternatives that apply different functions
//! ([`different_functions`]) at the first whose head is not the first's.

use std::borrow::Cow;

use krs_ir::{
    Arguments, AtLeastTwo, Descriptor, DescriptorPayload, DescriptorTerm, NamedTermArgument,
    ProvenanceKey, SentenceKind,
};

use super::error::DescriptorLoweringError;
use super::origin::key_range;

/// Moves the alternatives at each equation's subject root into the one
/// argument where they differ.
///
/// # Errors
///
/// Returns [`DescriptorLoweringError::InvalidPatternOr`] for alternatives
/// of one head that differ in more than one argument, or write their
/// arguments differently.
pub(super) fn distribute_root_alternatives(
    descriptors: Vec<Cow<'_, Descriptor>>,
) -> Result<Vec<Cow<'_, Descriptor>>, DescriptorLoweringError> {
    descriptors
        .into_iter()
        .map(|descriptor| {
            let DescriptorPayload::StructuredRule(rule) = descriptor.payload() else {
                return Ok(descriptor);
            };
            let DescriptorTerm::Or { key, .. } = &rule.subject else {
                return Ok(descriptor);
            };
            if rule.sentence_kind != SentenceKind::Equation {
                return Ok(descriptor);
            }
            let whole = root_alternatives(&rule.subject);
            let Some(subject) = distribute(&descriptor, key, &whole)? else {
                return Ok(descriptor);
            };
            let mut rule = rule.clone();
            rule.subject = subject;
            Ok(Cow::Owned(descriptor.with_distributed_alternatives(
                DescriptorPayload::StructuredRule(rule),
            )))
        })
        .collect()
}

/// The alternatives of `term`, an or-pattern nested at its root read as the
/// alternatives it joins.
fn flatten<'t>(term: &'t DescriptorTerm, output: &mut Vec<&'t DescriptorTerm>) {
    if let DescriptorTerm::Or { alternatives, .. } = term {
        for alternative in alternatives.iter() {
            flatten(alternative, output);
        }
    } else {
        output.push(term);
    }
}

/// The alternatives of an or-pattern at an equation's root, flattened.
pub(super) fn root_alternatives(subject: &DescriptorTerm) -> Vec<&DescriptorTerm> {
    let mut whole = Vec::new();
    flatten(subject, &mut whole);
    whole
}

/// The refusal of root alternatives that each apply a function, but not one
/// function: at the first whose head is not the first's.
pub(super) fn different_functions(
    descriptor: &Descriptor,
    alternatives: &[&DescriptorTerm],
) -> Option<DescriptorLoweringError> {
    let [first, rest @ ..] = alternatives else {
        return None;
    };
    let head = Head::of(first)?;
    rest.iter()
        .filter_map(|alternative| Head::of(alternative))
        .find(|other| !head.same_function(other))
        .map(|other| DescriptorLoweringError::InvalidPatternOr {
            item: Box::new(descriptor.id().clone()),
            reason: format!(
                "an equation defines one function, and every alternative of its whole subject applies it, but this alternative applies `{}` and the first applies `{}`; write an equation per function",
                other.name(),
                head.name(),
            ),
            range: key_range(descriptor, other.key).map(Box::new),
        })
}

/// The application the alternatives of the or-pattern `key` denote, with
/// their difference written in the one argument where they differ, or `None`
/// when they apply no one head (an alternative is no application, or two
/// apply different heads), which the root's check reports.
fn distribute(
    descriptor: &Descriptor,
    key: &ProvenanceKey,
    alternatives: &[&DescriptorTerm],
) -> Result<Option<DescriptorTerm>, DescriptorLoweringError> {
    let refuse = |at: &ProvenanceKey, reason: String| DescriptorLoweringError::InvalidPatternOr {
        item: Box::new(descriptor.id().clone()),
        reason,
        range: key_range(descriptor, at).map(Box::new),
    };
    let [first, rest @ ..] = alternatives else {
        unreachable!("an or-pattern has at least two alternatives");
    };
    let Some(head) = Head::of(first) else {
        return Ok(None);
    };
    let mut heads = Vec::with_capacity(rest.len());
    for alternative in rest {
        match Head::of(alternative) {
            Some(other) if head.same_function(&other) => heads.push((alternative, other)),
            _ => return Ok(None),
        }
    }
    let mut differing = None;
    for (alternative, other) in heads {
        let Some(arguments) = head.slots(&other) else {
            return Err(refuse(
                term_key(alternative),
                "the alternatives of an equation's whole subject write their arguments differently (in order or by field name, with or without `..`), so they are not compared argument by argument; write them alike".to_owned(),
            ));
        };
        for (index, (left, right)) in arguments.into_iter().enumerate() {
            if same(left, right) || differing == Some(index) {
                continue;
            }
            if differing.is_some() {
                return Err(refuse(key, SEVERAL_ARGUMENTS.to_owned()));
            }
            differing = Some(index);
        }
    }
    let Some(index) = differing else {
        return Ok(Some((*first).clone()));
    };
    let values = alternatives
        .iter()
        .map(|alternative| {
            Head::of(alternative)
                .and_then(|other| head.slots(&other))
                .and_then(|slots| slots.get(index).map(|(_, value)| (*value).clone()))
                .expect("every alternative was compared argument by argument")
        })
        .collect::<Vec<_>>();
    let or = DescriptorTerm::Or {
        key: key.clone(),
        alternatives: AtLeastTwo::try_from(values)
            .expect("an or-pattern has at least two alternatives"),
    };
    Ok(Some(with_argument(first, index, or)))
}

const SEVERAL_ARGUMENTS: &str = "these alternatives of an equation's whole subject differ in more than one argument; an equation matches each argument on its own, so `F(a, b) | F(c, d)` is not `F(a | c, b | d)`, which also matches `F(a, d)`: write the alternatives in the one argument where they differ, or write one equation per alternative";

/// The provenance key of a term's root node.
fn term_key(term: &DescriptorTerm) -> &ProvenanceKey {
    match term {
        DescriptorTerm::Variable { key, .. }
        | DescriptorTerm::Literal { key, .. }
        | DescriptorTerm::Wildcard { key }
        | DescriptorTerm::BuiltinToken { key, .. }
        | DescriptorTerm::Anonymous { key, .. }
        | DescriptorTerm::OrBool { key, .. }
        | DescriptorTerm::Cell { key, .. }
        | DescriptorTerm::Lexeme { key, .. }
        | DescriptorTerm::SortTest { key, .. }
        | DescriptorTerm::As { key, .. }
        | DescriptorTerm::Or { key, .. }
        | DescriptorTerm::Matches { key, .. }
        | DescriptorTerm::Let { key, .. }
        | DescriptorTerm::Closure { key, .. }
        | DescriptorTerm::Rewrite { key, .. } => key,
        DescriptorTerm::Application { reference, .. } => &reference.key,
    }
}

/// The head of an alternative: the application it is, read without its
/// provenance.
struct Head<'t> {
    key: &'t ProvenanceKey,
    application: &'t krs_ir::DescriptorApplicationRef,
    instance: &'t [krs_ir::DescriptorSortReference],
    arguments: &'t Arguments<krs_ir::DescriptorStage>,
    open: bool,
}

impl<'t> Head<'t> {
    /// The application `term` is, unless it is a record update, which no
    /// pattern holds.
    fn of(term: &'t DescriptorTerm) -> Option<Self> {
        match term {
            DescriptorTerm::Application {
                reference,
                arguments,
                instance,
                update: None,
                open,
                ..
            } => Some(Self {
                key: &reference.key,
                application: &reference.application,
                instance,
                arguments,
                open: *open,
            }),
            _ => None,
        }
    }

    /// Whether `other` applies the same function at the same instance.
    fn same_function(&self, other: &Self) -> bool {
        self.application == other.application
            && self.instance.len() == other.instance.len()
            && self
                .instance
                .iter()
                .zip(other.instance)
                .all(|(left, right)| left.sort == right.sort)
    }

    /// The function's name, for a diagnostic.
    fn name(&self) -> String {
        match self.application {
            krs_ir::DescriptorApplicationRef::Declared(id) => id.item_name().to_owned(),
            other => format!("{other:?}"),
        }
    }

    /// This head's arguments paired with `other`'s, in this head's order:
    /// by position, or by field identity, when both write them alike.
    fn slots(&self, other: &Self) -> Option<Vec<(&'t DescriptorTerm, &'t DescriptorTerm)>> {
        if self.open != other.open || self.arguments.len() != other.arguments.len() {
            return None;
        }
        match (self.arguments, other.arguments) {
            (Arguments::Positional(left), Arguments::Positional(right)) => Some(
                left.iter()
                    .zip(right)
                    .map(|(left, right)| (&**left, &**right))
                    .collect(),
            ),
            (Arguments::Named(left), Arguments::Named(right)) => left
                .iter()
                .map(|left| {
                    right
                        .iter()
                        .find(|right| right.field == left.field)
                        .map(|right| (&*left.value, &*right.value))
                })
                .collect(),
            _ => None,
        }
    }
}

/// `term`, an application, with `value` as its argument at `index`.
fn with_argument(term: &DescriptorTerm, index: usize, value: DescriptorTerm) -> DescriptorTerm {
    let mut term = term.clone();
    let mut value = Some(value);
    let mut at = |position: usize, argument: &DescriptorTerm| {
        Box::new(if position == index {
            value.take().expect("one argument is at `index`")
        } else {
            argument.clone()
        })
    };
    if let DescriptorTerm::Application { arguments, .. } = &mut term {
        *arguments = match &*arguments {
            Arguments::Positional(values) => Arguments::Positional(
                values
                    .iter()
                    .enumerate()
                    .map(|(position, argument)| at(position, argument))
                    .collect(),
            ),
            Arguments::Named(values) => Arguments::named(
                values
                    .iter()
                    .enumerate()
                    .map(|(position, argument)| NamedTermArgument {
                        key: argument.key.clone(),
                        field: argument.field.clone(),
                        value: at(position, &argument.value),
                    })
                    .collect(),
            ),
        };
    }
    term
}

/// Whether two patterns are one pattern, read without their provenance: a
/// name is the binder it names, and `_` matches what any `_` matches. A
/// construct this does not compare counts as different, which only refuses
/// alternatives that might have distributed.
fn same(left: &DescriptorTerm, right: &DescriptorTerm) -> bool {
    match (left, right) {
        (
            DescriptorTerm::Variable { name: left, .. },
            DescriptorTerm::Variable { name: right, .. },
        ) => left == right,
        (DescriptorTerm::Wildcard { .. }, DescriptorTerm::Wildcard { .. }) => true,
        (
            DescriptorTerm::Literal { literal: left, .. },
            DescriptorTerm::Literal { literal: right, .. },
        ) => left == right,
        (
            DescriptorTerm::BuiltinToken {
                sort: left_sort,
                value: left,
                ..
            },
            DescriptorTerm::BuiltinToken {
                sort: right_sort,
                value: right,
                ..
            },
        ) => left_sort == right_sort && left == right,
        (
            DescriptorTerm::Lexeme {
                sort: left_sort,
                text: left,
                ..
            },
            DescriptorTerm::Lexeme {
                sort: right_sort,
                text: right,
                ..
            },
        ) => left_sort.sort == right_sort.sort && left == right,
        (
            DescriptorTerm::As {
                name: left_name,
                pattern: left,
                ..
            },
            DescriptorTerm::As {
                name: right_name,
                pattern: right,
                ..
            },
        ) => left_name == right_name && same(left, right),
        (
            DescriptorTerm::Or {
                alternatives: left, ..
            },
            DescriptorTerm::Or {
                alternatives: right,
                ..
            },
        ) => left.len() == right.len() && left.iter().zip(right.iter()).all(|(l, r)| same(l, r)),
        (DescriptorTerm::Application { .. }, DescriptorTerm::Application { .. }) => {
            match (Head::of(left), Head::of(right)) {
                (Some(left), Some(right)) => {
                    left.same_function(&right)
                        && left
                            .slots(&right)
                            .is_some_and(|slots| slots.into_iter().all(|(l, r)| same(l, r)))
                }
                _ => false,
            }
        }
        _ => false,
    }
}
