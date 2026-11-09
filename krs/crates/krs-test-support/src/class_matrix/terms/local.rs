//! Where a term case has a case through a local ([`super::super::through`]), and how KRS writes
//! the block there.
//!
//! The block `{ let y = S; y }` means what `S` means where a block stands, so the rule holds at a
//! position exactly where the block itself means something and reads `S` as `S` is read there:
//!
//! - where a term is built or a condition computed ([`Kind::Built`], [`Kind::Guard`]). A pattern
//!   holds no block, which the oracle refuses there as its own mistake (`let-outside-term`); and a
//!   key a pattern computes ([`Kind::Evaluated`]) reads two ways, a selection where its construct
//!   is pattern-only or a name nothing else binds and a lookup where it computes, while a block is
//!   a computed term, looked up: it would turn `S`'s selection into a lookup, another meaning.
//! - not below a key or a set's element a pattern computes, where the key's notation is read as
//!   the key's at every depth (`A | B` is alternatives there, R-K1, and `[x, ..]` a list pattern's
//!   rest), while a block's value is a term built whatever stands around it ([`in_pattern_key`]).
//! - where the oracle admits the block itself ([`admits_block`]): not in a constant's value, a
//!   ground term, which a block (the application of the function K's `#let` is) is not, nor
//!   where the oracle refuses a block for any other reason of the position.
//! - for a construct that names a value: a matching-logic predicate at a condition is a formula,
//!   which a claim's or a simplification's condition holds and a transition's refuses as one,
//!   while the block's result is an object term, which the predicate would be an operand of
//!   ([`super::super::positions::Opening::LetBody`]): another construct. A cell fragment,
//!   `k::fragment![..]`, is cell-state notation, the cells a position holds, and no value of a
//!   sort that a local could name.
//!
//! The spellings the slot holds are the direct case's: the block reads no name `S` does not, so
//! a slot that holds the spellings reading `x` (an alias root's) holds their blocks too.
//!
//! Two blocks are written, by one rule: a local names its value, and a block denotes its result.
//! `{ let y = S; y }` at every such position, depth 2 included ([`Family::TermsLocal`]), and
//! `{ let y = { S }; y }`, a local whose value is itself a block, at the positions of depth 1 and
//! the slots' roots ([`Family::TermsLocalBlock`]): the second asks whether the value a local
//! names is read through a block as `S` is, which the position's own sort decides, while a depth-2
//! position is another construct's operand, whose reading through a local the first block
//! already asks there.

use super::super::oracle::{self, Outcome};
use super::super::positions::Construct as C;
use super::super::positions::Opening::{LetBody, LetPattern, LetValue};
use super::super::positions::{Entry, Form, Kind, Node, Position, Slot as Part, node};
use super::super::{Case, Family};
use super::{Slot, Spelling, case_of};

/// The text a construct through a local of `family` is written in, before and after it.
pub(super) const fn around(family: Family) -> (&'static str, &'static str) {
    match family {
        Family::TermsLocalBlock | Family::NotationLocalBlock => ("{ let y = { ", " }; y }"),
        _ => ("{ let y = ", "; y }"),
    }
}

/// The cases through a local of the case of `spelling` at `slot` in `family` (a term or a
/// notation case): one per block the rule writes there ([module docs](self)).
pub(super) fn derived(family: Family, slot: &Slot, spelling: &Spelling) -> Vec<Case> {
    let Some(differs) = through(slot, spelling) else {
        return Vec::new();
    };
    let (local, block) = match family {
        Family::Terms => (Family::TermsLocal, Family::TermsLocalBlock),
        Family::Notation => (Family::NotationLocal, Family::NotationLocalBlock),
        _ => return Vec::new(),
    };
    let mut cases = vec![case_of(local, slot, spelling, Some(differs))];
    if slot.opener.is_none() {
        cases.push(case_of(block, slot, spelling, Some(differs)));
    }
    cases
}

/// Why K7 does not run a case through a local written in place ([`super::super::through`]).
pub(super) const JUDGED_BY_DIRECT: &str = "a case through a local, whose K, read through the block, \
     K3 compares with its direct case's, which K6 and K7 judge";

/// Why a claim's block gives other K.
const CLAIM: &str = "a claim's states and conditions hold a block as the application of a \
     function KRS lifts it into, `krsLocal_<digest>(..)`, whose one equation's result is the \
     block";

/// Why a static clause's result's block gives other K.
const STATIC_RESULT: &str = "an alias's or a desugar's result holds a block as the application \
     of a function KRS lifts it into, `krsLocal_<digest>(..)`, whose one equation's result is the \
     block";

/// Why a projection through a local gives other K.
const PROJECTION: &str = "a sort projection standing where its sort test can be the sentence's \
     condition is lowered as its operand under that test, and in a block's value as the cast, \
     guarded alike: the same value, other K";

/// Why a framed map result's key through a local gives other K.
const FRAMED_KEY: &str = "a key a framed `cells!` result writes over the map its subject frames is \
     compared with the key the subject matched, and written as that entry where it is the matched \
     name; a block is no name, so the result is the update of the remainder: the same map, other K";

/// The nodes of the block `{ let y = x; y }` at the hole.
fn block() -> [Node; 4] {
    [
        node(C::Let, &[]),
        node(C::Reference, &[LetPattern]),
        node(C::Reference, &[LetValue]),
        node(C::Reference, &[LetBody]),
    ]
}

/// Whether the oracle admits a block at `hole`, whatever its value.
fn admits_block(hole: Position) -> bool {
    oracle::expected(hole, &block()) == Outcome::Accept
}

/// Whether `hole` lies in a key or a set's element a pattern reads, whose notation is the key's at
/// every depth ([module docs](self)).
fn in_pattern_key(hole: Position) -> bool {
    hole.slot == Part::Subject
        && (hole.nesting.entries.contains(Entry::MapKey)
            || hole.nesting.entries.contains(Entry::SetElement))
}

/// Why a case through a local has other K than its direct case beyond the block, where it does;
/// `None` where it does not ([`super::super::through::Through::differs`]).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Differs(pub(super) Option<&'static str>);

/// Whether the case of `spelling` at `slot` has a case through a local, and if so, why its K
/// differs from its direct case's beyond the block.
pub(super) fn through(slot: &Slot, spelling: &Spelling) -> Option<Differs> {
    let hole = slot.at.enter_all(&slot.hole);
    let root = spelling.nodes.first().map(|node| node.construct);
    let predicate_at_condition = hole.kind == Kind::Guard && root == Some(C::MlPredicate);
    let fragment = root == Some(C::Fragment);
    (matches!(hole.kind, Kind::Built | Kind::Guard)
        && !in_pattern_key(hole)
        && admits_block(hole)
        && !predicate_at_condition
        && !fragment)
        .then(|| Differs(differs(slot, spelling, hole)))
}

/// Why the K of a case through a local at `hole` differs from its direct case's beyond the
/// block: KRS lifts a block into a function in a claim's states and conditions and in a static
/// clause's result (the reference's "Local bindings"), and lowers two constructs by their
/// spelling around them, a projection and a framed map result's key. A `k::rewrite!`'s right
/// side, inside a single-body rule's subject, is built in place.
fn differs(slot: &Slot, spelling: &Spelling, hole: Position) -> Option<&'static str> {
    if hole.form.is_claim() {
        Some(CLAIM)
    } else if matches!(hole.form, Form::Alias | Form::Desugar) && hole.slot == Part::Result {
        Some(STATIC_RESULT)
    } else if spelling
        .nodes
        .iter()
        .any(|node| node.construct == C::Projection)
    {
        Some(PROJECTION)
    } else if slot.position.starts_with("result-map-framed") {
        Some(FRAMED_KEY)
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::super::{notation_spellings, slots, spellings};
    use super::*;

    /// The oracle, which states what each construct means where it stands, reads the block as
    /// its value wherever [`through`] writes one: the block's nodes around the spelling's, at the
    /// slot's hole, give the oracle's outcome of the spelling alone. So the rule that a case
    /// through a local is expected what its direct case is agrees with the generator's own
    /// meaning of each construct, case by case.
    #[test]
    fn the_oracle_reads_every_block_a_case_through_a_local_writes_as_its_value() {
        let mut disagreements = Vec::new();
        let mut derived = 0;
        for slot in slots() {
            for spelling in spellings().iter().chain(&notation_spellings()) {
                if !slot.holds.admits(spelling.text(slot.at.form))
                    || !spelling.stands_at(&slot)
                    || through(&slot, spelling).is_none()
                {
                    continue;
                }
                derived += 1;
                let with = |inner: Vec<Node>| {
                    let mut nodes = slot.before.clone();
                    nodes.extend(inner.into_iter().map(|node| node.below(&slot.hole)));
                    nodes.extend(slot.after.iter().cloned());
                    oracle::expected(slot.at, &nodes)
                };
                let direct = with(spelling.nodes.clone());
                // `{ let y = S; y }`, and `{ let y = { S }; y }`, whose value is a block of no
                // statement.
                let mut local = vec![block()[0].clone(), block()[1].clone()];
                local.extend(spelling.nodes.iter().map(|node| node.below(&[LetValue])));
                local.push(block()[3].clone());
                let mut valued = vec![
                    block()[0].clone(),
                    block()[1].clone(),
                    node(C::Let, &[LetValue]),
                ];
                valued.extend(
                    spelling
                        .nodes
                        .iter()
                        .map(|node| node.below(&[LetValue, LetBody])),
                );
                valued.push(block()[3].clone());
                let class = |outcome: Outcome| match outcome {
                    Outcome::Accept => "accept",
                    Outcome::Refuse(refusal) => refusal.class.name(),
                };
                for (variant, nodes) in [("a local", local), ("a local's block", valued)] {
                    let derived_outcome = with(nodes);
                    if class(direct) != class(derived_outcome) {
                        disagreements.push(format!(
                            "{}/{}{}/{}: {} directly, {} through {variant}",
                            slot.form,
                            slot.position,
                            slot.opener
                                .map(|opener| format!("/{opener}"))
                                .unwrap_or_default(),
                            spelling.text(slot.at.form),
                            class(direct),
                            class(derived_outcome)
                        ));
                    }
                }
            }
        }
        assert!(derived > 0);
        assert!(
            disagreements.is_empty(),
            "{} of {derived}:\n{}",
            disagreements.len(),
            disagreements.join("\n")
        );
    }
}
