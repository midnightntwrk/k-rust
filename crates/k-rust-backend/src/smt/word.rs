//! Guarded finite readings of complete scalar expressions, preserving mathematical Int values.
//!
//! Bounds select a representation; they are repeated in the emitted guard, never asserted.
//! Each integer node has an inclusive interval and enough bits for every value in it. Arithmetic
//! extends before computing; only explicit source projections discard bits. All intermediate
//! nodes are lexical lets. Unsupported operations, quantifiers and resource limits retain the
//! ordinary translation, including its exactness/model restrictions and original definedness.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use k_rust_kore::names::BuiltinSort;
use num_bigint::{BigInt, Sign};
use num_traits::{One, Zero};
use rustc_hash::FxHashMap;

use super::summary::{self, Atom, Decision, Key, Reading, Summary};
use super::{SExpr, TranslationError, TranslationState};
use crate::{
    builtin::{read_bool, read_int},
    rule::Predicate,
    stop::{self, Stoppable},
    term::{Term, TermKind, VariableKind},
};

#[cfg(test)]
mod tests;

const WIDTH_LIMIT: u32 = 256;
const DEPTH_LIMIT: usize = 128;
const WORK_LIMIT: usize = 32_768;
const NODE_LIMIT: usize = 4096;
const TEXT_LIMIT: usize = 1_048_576;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Interval {
    lo: BigInt,
    hi: BigInt,
}

impl Interval {
    fn literal(value: BigInt) -> Self {
        Self {
            lo: value.clone(),
            hi: value,
        }
    }

    fn unsigned(width: u32) -> Self {
        Self {
            lo: BigInt::zero(),
            hi: (BigInt::one() << width) - 1,
        }
    }

    fn signed(&self) -> bool {
        self.lo.sign() == Sign::Minus
    }

    fn width(&self) -> Option<u32> {
        if self.lo > self.hi {
            return None;
        }
        let bits = if self.signed() {
            // -2^(w-1) <= lo, hi < 2^(w-1).
            ((!&self.lo).bits().max(self.hi.bits())) + 1
        } else {
            self.hi.bits().max(1)
        };
        u32::try_from(bits).ok().filter(|w| *w <= WIDTH_LIMIT)
    }

    fn union(&self, other: &Self) -> Self {
        Self {
            lo: self.lo.clone().min(other.lo.clone()),
            hi: self.hi.clone().max(other.hi.clone()),
        }
    }
}

fn app(op: impl Into<String>, args: Vec<SExpr>) -> SExpr {
    SExpr::application(op, args)
}
fn atom(value: impl ToString) -> SExpr {
    SExpr::atom(value.to_string())
}
// Reject oversized text before allocating a BigInt; larger values use scalar translation.
fn integer(term: &Term) -> Option<BigInt> {
    let TermKind::DomainValue { value, .. } = term.kind() else {
        return None;
    };
    if value.as_utf8().ok()?.len() > 80 {
        return None;
    }
    read_int(term)
}

fn reference(id: usize) -> SExpr {
    atom(format!("KRUST-WORD-{id}"))
}
fn literal(value: &BigInt, width: u32) -> SExpr {
    let value = value & ((BigInt::one() << width) - 1);
    atom(format!("(_ bv{value} {width})"))
}

enum Value {
    Input(Term),
    Parameter(String),
    Expression(SExpr),
}

struct Node {
    value: Value,
    // None is Bool; Some is a full mathematical Int value, not a modular interpretation.
    interval: Option<Interval>,
    level: usize,
}

struct Plan {
    nodes: Vec<Node>,
    used: BTreeMap<Term, Interval>,
    root: usize,
    interesting: bool,
}

struct Planner<'a> {
    bounds: &'a BTreeMap<Term, Interval>,
    remaining: &'a mut usize,
    memo: FxHashMap<Term, usize>,
    decisions: FxHashMap<*const Decision, usize>,
    plan: Plan,
    registry: Option<&'a mut Registry>,
    opaque_boolean_inputs: bool,
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
struct Profile {
    key: Key,
    arguments: Vec<Option<Interval>>,
}

#[derive(Clone)]
struct Variant {
    name: String,
    interval: Option<Interval>,
}

struct Definition {
    name: String,
    parameters: Vec<(String, Option<Interval>)>,
    plan: Plan,
}

struct Registry {
    source: BTreeMap<Key, Reading>,
    variants: BTreeMap<Profile, Option<Variant>>,
    definitions: Vec<Definition>,
    active: usize,
    counter: usize,
}

impl Registry {
    fn new(source: BTreeMap<Key, Reading>) -> Self {
        Self {
            source,
            variants: BTreeMap::new(),
            definitions: Vec::new(),
            active: 0,
            counter: 0,
        }
    }

    fn variant(
        &mut self,
        source: &Summary,
        arguments: Vec<Option<Interval>>,
        remaining: &mut usize,
        depth: usize,
    ) -> Stoppable<Option<Variant>> {
        stop::check()?;
        let profile = Profile {
            key: source.key.clone(),
            arguments,
        };
        if let Some(found) = self.variants.get(&profile) {
            return Ok(found.clone());
        }
        if self.counter >= 128 || self.active >= 64 || *remaining == 0 || depth >= DEPTH_LIMIT {
            return Ok(None);
        }
        let name = format!("SMT-WORD-{}", self.counter);
        self.counter += 1;
        self.active += 1;
        let bounds = BTreeMap::new();
        let mut planner = Planner {
            bounds: &bounds,
            remaining,
            memo: FxHashMap::default(),
            decisions: FxHashMap::default(),
            plan: Plan {
                nodes: Vec::new(),
                used: BTreeMap::new(),
                root: 0,
                interesting: false,
            },
            registry: Some(self),
            opaque_boolean_inputs: false,
        };
        let mut parameters = Vec::new();
        let mut complete = true;
        for (index, (formal, range)) in source.parameters.iter().zip(&profile.arguments).enumerate()
        {
            stop::check()?;
            let name = format!("KRUST-WORD-PARAM-{index}");
            let Some(id) = planner.push(Value::Parameter(name.clone()), range.clone()) else {
                complete = false;
                break;
            };
            planner.memo.insert(Term::variable(formal.clone()), id);
            parameters.push((name, range.clone()));
        }
        let result = if complete {
            planner.decision(&source.body, depth + 1)?
        } else {
            None
        };
        let plan = planner.plan;
        self.active -= 1;
        let Some(root) = result else {
            self.variants.insert(profile, None);
            return Ok(None);
        };
        let interval = plan.nodes[root].interval.clone();
        let mut plan = plan;
        plan.root = root;
        let variant = Variant {
            name: name.clone(),
            interval,
        };
        self.definitions.push(Definition {
            name,
            parameters,
            plan,
        });
        self.variants.insert(profile, Some(variant.clone()));
        Ok(Some(variant))
    }

    fn emit(
        self,
        state: &mut TranslationState,
        text: &mut usize,
    ) -> Stoppable<Result<bool, TranslationError>> {
        for definition in self.definitions {
            stop::check()?;
            let result = definition.plan.nodes[definition.plan.root].interval.clone();
            let sort = |range: Option<Interval>| {
                range.map_or_else(
                    || "Bool".to_owned(),
                    |r| format!("(_ BitVec {})", r.width().expect("checked profile width")),
                )
            };
            let parameters = definition
                .parameters
                .into_iter()
                .map(|(name, range)| SExpr::List(vec![atom(name), atom(sort(range))]))
                .collect();
            let body = match emit_nodes(definition.plan.nodes, definition.plan.root, state)? {
                Ok(body) => body,
                Err(error) => return Ok(Err(error)),
            };
            let reading =
                reading_definition(state, definition.name, parameters, atom(sort(result)), body)?;
            if !fits_text(&reading.command, text)? {
                return Ok(Ok(false));
            }
            install_reading(state, reading);
        }
        Ok(Ok(true))
    }
}

/// The command that defines a reading (a word variant, a scalar summary or its domain), before
/// [`install_reading`] adds it to the query.
pub(super) struct ReadingDefinition {
    name: String,
    /// Whether the command is a `define-fun`.
    macro_definition: bool,
    command: SExpr,
}

impl ReadingDefinition {
    pub(super) fn command(&self) -> &SExpr {
        &self.command
    }
}

/// The definition of reading `name` as `body` over `parameters`, of sort `sort`.
///
/// No reading applies itself, directly or through others: the admitted source graph is acyclic
/// (`summary`), and a word variant applies only variants completed before it. So a reading is a
/// definition, and `define-fun` states it as one: Z3 replaces each application by the body while
/// it reads the script, and the search sees the body with the rest of the assertions, rewritten
/// with them before search. `define-fun-rec` instead declares a function and its defining
/// axiom; Z3 unfolds an application during search and rewrites the unfolded body there, where
/// the check's cancellation can cut the rewrite short ([`internalized_operators`]).
///
/// The replacement copies the body once per distinct application, and the body itself holds the
/// copies of the `define-fun` readings it applies, so `define-fun` readings applying one another
/// would grow with the product of their applications: `n` levels each applying the level below
/// at two distinct arguments copy the lowest body `2^n` times, while Z3 reads the script, before
/// any limit of the check applies. A reading is therefore a `define-fun` exactly when its body
/// applies no `define-fun` reading. The expansion of such a body is then its text with each
/// application of a power definition (`|KRUST-POWER-VALUE|`, `|KRUST-POWER-OF-b|`, which are
/// `define-fun`s applying no definition) replaced by that definition's text, and the expansion
/// of a script is bounded by its text with each application of a reading or a power definition
/// replaced by that definition's text. Any other reading is a `define-fun-rec`, whose
/// applications stay single terms until search unfolds them, as the applications of a declared
/// function do.
///
/// Both kinds of body are written in operators Z3's search internalizes as written
/// ([`internalized_operators`]): a `define-fun-rec` body is unfolded during search, and a
/// `define-fun` body is copied into the `define-fun-rec` bodies that apply it.
pub(super) fn reading_definition(
    state: &TranslationState,
    name: String,
    parameters: Vec<SExpr>,
    sort: SExpr,
    body: SExpr,
) -> Stoppable<ReadingDefinition> {
    let body = internalized_operators(body)?;
    let mut pending = vec![&body];
    let mut applies_macro = false;
    while let Some(expression) = pending.pop() {
        stop::check()?;
        match expression {
            SExpr::Atom(text) => {
                if state.reading_macros.contains(super::symbol_name(text)) {
                    applies_macro = true;
                    break;
                }
            }
            SExpr::List(children) => pending.extend(children),
        }
    }
    let command = app(
        if applies_macro {
            "define-fun-rec"
        } else {
            "define-fun"
        },
        vec![atom(&name), SExpr::List(parameters), sort, body],
    );
    Ok(ReadingDefinition {
        name,
        macro_definition: !applies_macro,
        command,
    })
}

/// `body` with every application of an operator that Z3's search does not internalize as
/// written replaced by its meaning in operators it does, where SMT-LIB defines one exactly.
///
/// Z3 internalizes a term or an atom in the search only in the operators its theories and its core
/// take as written: in the bit-vector theory, the arithmetic and bitwise operations, shifts,
/// extractions, extensions, `int2bv` and `bv2nat`, and of the comparisons only `bvule` and `bvsle`
/// (`theory_bv::internalize_term` and `internalize_atom`); in the core, `not`, `and`, `or`, `ite`,
/// `=` and `xor` of two operands, and from Z3 4.15.3 on also `=>` (`context::internalize_formula`).
/// Every other operator must have been rewritten into those first. The search rewrites the body of
/// a `define-fun-rec` application when it unfolds it (`theory_recfun::apply_args`), and the check's
/// cancellation (its resource limit or timeout) can cut that rewrite short and leave the rest of
/// the body as written. An operator left so is an internal error of Z3: a bit-vector one reaches
/// the `UNREACHABLE` of its theory (Z3 4.12.5 ends the process with exit status 114, 4.16.0 and
/// 5.3.3 answer unknown with the reason `unreachable`), and a core one reaches the core's
/// `formula has not been simplified` exception. Which core operators that is depends on the
/// version: Z3 4.12.5 refuses `=>` and `distinct`, while 4.16.0 and 5.3.3 refuse `distinct` but
/// internalize `=>` (`context::mk_implies_cnstr`); all three refuse `=` over Bool and `xor` with
/// more than two operands (`context::mk_iff_cnstr`). A Game Boy CPU specification met the
/// bit-vector case through a `bvult`.
///
/// The word planner writes only internalized operators, `=` and `xor` with two operands. This
/// rewrites the rest of the text a reading copies, from the ordinary translation of its inputs and
/// from the definition's `smt-hook`s (`distinct` for `INT.ne`, say), exactly: `(=> a ... b)` is
/// `(or (not a) ... b)` (a rewrite 4.16.0 and 5.3.3 do not need and 4.12.5 does),
/// `(distinct a b ...)` is the conjunction of `(not (= a b))` over its pairs, and over the total
/// orders of bit-vectors `a < b` is `(not (b <= a))`, `a > b` is `(not (a <= b))` and `a >= b` is
/// `(b <= a)`. Arithmetic
/// needs no rewrite: Z3's arithmetic theory reads an atom or a term it does not internalize as
/// unsupported, which makes the check's answer unknown (`theory_lra::internalize_atom`), never an
/// internal error. An operator outside all of these can reach a reading only through an `smt-hook`
/// template (a bit-vector division, say), whose meaning in the internalized operators this does not
/// know; the cut-short rewrite can leave it as written, which is then the internal error above.
fn internalized_operators(body: SExpr) -> Stoppable<SExpr> {
    enum Step {
        Visit(SExpr),
        Build(usize),
    }
    let mut steps = vec![Step::Visit(body)];
    let mut built = Vec::new();
    while let Some(step) = steps.pop() {
        stop::check()?;
        match step {
            Step::Visit(SExpr::List(children)) => {
                steps.push(Step::Build(children.len()));
                steps.extend(children.into_iter().rev().map(Step::Visit));
            }
            Step::Visit(atom) => built.push(atom),
            Step::Build(length) => {
                let children = built.split_off(built.len() - length);
                built.push(internalized_application(children));
            }
        }
    }
    Ok(built.pop().expect("the body was built"))
}

/// The list `children`, whose children are already rewritten by [`internalized_operators`], as
/// an application of an internalized operator.
fn internalized_application(mut children: Vec<SExpr>) -> SExpr {
    let operator = match children.first() {
        Some(SExpr::Atom(operator)) => operator.as_str(),
        _ => return SExpr::List(children),
    };
    let order = match operator {
        "bvult" | "bvugt" | "bvuge" => Some("bvule"),
        "bvslt" | "bvsgt" | "bvsge" => Some("bvsle"),
        _ => None,
    };
    if let Some(le) = order {
        if children.len() != 3 {
            return SExpr::List(children);
        }
        let swapped = !matches!(operator, "bvugt" | "bvsgt");
        let negated = !matches!(operator, "bvuge" | "bvsge");
        let right = children.pop().expect("two operands");
        let left = children.pop().expect("two operands");
        let comparison = if swapped {
            app(le, vec![right, left])
        } else {
            app(le, vec![left, right])
        };
        return if negated {
            app("not", vec![comparison])
        } else {
            comparison
        };
    }
    match operator {
        "=>" if children.len() >= 3 => {
            let conclusion = children.pop().expect("a conclusion");
            let mut disjuncts = children
                .into_iter()
                .skip(1)
                .map(|premise| app("not", vec![premise]))
                .collect::<Vec<_>>();
            disjuncts.push(conclusion);
            app("or", disjuncts)
        }
        "distinct" if children.len() >= 3 => {
            let operands = children.split_off(1);
            let mut different = Vec::new();
            for (index, left) in operands.iter().enumerate() {
                for right in &operands[index + 1..] {
                    different.push(app(
                        "not",
                        vec![app("=", vec![left.clone(), right.clone()])],
                    ));
                }
            }
            if different.len() == 1 {
                different.pop().expect("one pair")
            } else {
                app("and", different)
            }
        }
        _ => SExpr::List(children),
    }
}

/// Add `reading` to the query's derived definitions.
pub(super) fn install_reading(state: &mut TranslationState, reading: ReadingDefinition) {
    state.derived_definitions.push(reading.command.to_string());
    if reading.macro_definition {
        state.reading_macros.insert(reading.name);
    }
}

impl Planner<'_> {
    fn decision(&mut self, decision: &Decision, depth: usize) -> Stoppable<Option<usize>> {
        stop::check()?;
        if depth >= DEPTH_LIMIT || *self.remaining == 0 {
            return Ok(None);
        }
        *self.remaining -= 1;
        if let Some(id) = self.decisions.get(&std::ptr::from_ref(decision)) {
            return Ok(Some(*id));
        }
        let result = match decision {
            Decision::Value(term) => self.term(term, depth + 1),
            // An unconstrained value has no finite reading; the ordinary translation remains.
            Decision::Opaque => Ok(None),
            Decision::If { test, yes, no } => {
                let test = match test {
                    Atom::Bool(term) => self.term(term, depth + 1)?,
                    Atom::Less(a, b) | Atom::Equal(a, b) => {
                        match (self.term(a, depth + 1)?, self.term(b, depth + 1)?) {
                            (Some(a), Some(b)) => self.comparison(
                                if matches!(test, Atom::Less(..)) {
                                    "lt"
                                } else {
                                    "eq"
                                },
                                a,
                                b,
                            ),
                            _ => None,
                        }
                    }
                };
                let Some(test) = test else {
                    return Ok(None);
                };
                let Some(yes) = self.decision(yes, depth + 1)? else {
                    return Ok(None);
                };
                let Some(no) = self.decision(no, depth + 1)? else {
                    return Ok(None);
                };
                Ok(self.conditional(test, yes, no))
            }
        }?;
        if let Some(id) = result {
            self.decisions.insert(std::ptr::from_ref(decision), id);
        }
        Ok(result)
    }

    fn conditional(&mut self, a: usize, b: usize, c: usize) -> Option<usize> {
        let interval = match (self.range(b), self.range(c)) {
            (Some(b), Some(c)) => Some(b.union(c)),
            (None, None) => None,
            _ => return None,
        };
        let (yes, no) = if let Some(interval) = &interval {
            let width = interval.width()?;
            (self.resize(b, width)?, self.resize(c, width)?)
        } else {
            (reference(b), reference(c))
        };
        self.expression(
            app("ite", vec![reference(a), yes, no]),
            interval,
            &[a, b, c],
        )
    }

    fn helper(&mut self, call: &Term, depth: usize) -> Stoppable<Option<usize>> {
        let Some(source) = self
            .registry
            .as_ref()
            .and_then(|r| summary::reading(&r.source, call))
            .map(|r| r.summary.clone())
        else {
            return Ok(None);
        };
        // Preserve the paired scalar value/domain reading until this profile has a checked
        // word-domain lowering. In particular, a total helper's opaque fallback must never
        // be replaced by its partial source body outside the derived safe region.
        if !source.domain_total {
            return Ok(None);
        }
        let TermKind::Application { arguments, .. } = call.kind() else {
            unreachable!()
        };
        let mut ids = Vec::new();
        for (argument, static_argument) in arguments.iter().zip(&source.key.static_arguments) {
            if static_argument.is_none() {
                let Some(id) = self.term(argument, depth + 1)? else {
                    return Ok(None);
                };
                ids.push(id);
            }
        }
        let ranges = ids
            .iter()
            .map(|id| self.plan.nodes[*id].interval.clone())
            .collect();
        let Some(variant) = self
            .registry
            .as_deref_mut()
            .expect("helper registry")
            .variant(&source, ranges, self.remaining, depth + 1)?
        else {
            return Ok(None);
        };
        self.plan.interesting = true;
        let value = if ids.is_empty() {
            atom(variant.name)
        } else {
            app(variant.name, ids.iter().map(|id| reference(*id)).collect())
        };
        Ok(self.expression(value, variant.interval, &ids))
    }
    fn push(&mut self, value: Value, interval: Option<Interval>) -> Option<usize> {
        if self.plan.nodes.len() >= NODE_LIMIT {
            return None;
        }
        if let Some(interval) = &interval {
            interval.width()?;
        }
        let id = self.plan.nodes.len();
        self.plan.nodes.push(Node {
            value,
            interval,
            level: 0,
        });
        Some(id)
    }

    fn expression(
        &mut self,
        value: SExpr,
        interval: Option<Interval>,
        dependencies: &[usize],
    ) -> Option<usize> {
        let level = dependencies
            .iter()
            .map(|id| self.plan.nodes[*id].level + 1)
            .max()
            .unwrap_or(0);
        let id = self.push(Value::Expression(value), interval)?;
        self.plan.nodes[id].level = level;
        Some(id)
    }

    fn range(&self, id: usize) -> Option<&Interval> {
        self.plan.nodes[id].interval.as_ref()
    }

    fn resize(&self, id: usize, width: u32) -> Option<SExpr> {
        let range = self.range(id)?;
        let from = range.width()?;
        Some(if from == width {
            reference(id)
        } else if from < width {
            app(
                format!(
                    "(_ {} {})",
                    if range.signed() {
                        "sign_extend"
                    } else {
                        "zero_extend"
                    },
                    width - from
                ),
                vec![reference(id)],
            )
        } else {
            app(format!("(_ extract {} 0)", width - 1), vec![reference(id)])
        })
    }

    /// The comparison `op` of nodes `a` and `b`. An order comparison is written only with
    /// `bvule` or `bvsle`, negated or with its operands swapped: over a total order `a < b` is
    /// `(not (b <= a))`, `a > b` is `(not (a <= b))` and `a >= b` is `(b <= a)`, exactly. These
    /// two are the only comparisons Z3's search internalizes as written, which every operator of
    /// a reading's body must be ([`internalized_operators`]).
    fn comparison(&mut self, op: &str, a: usize, b: usize) -> Option<usize> {
        match (self.range(a), self.range(b)) {
            (Some(a_range), Some(b_range)) => {
                let combined = a_range.union(b_range);
                let width = combined.width()?;
                let le = if combined.signed() { "bvsle" } else { "bvule" };
                let (left, right) = (self.resize(a, width)?, self.resize(b, width)?);
                let value = match op {
                    "eq" => app("=", vec![left, right]),
                    "ne" => app("not", vec![app("=", vec![left, right])]),
                    "le" => app(le, vec![left, right]),
                    "ge" => app(le, vec![right, left]),
                    "lt" => app("not", vec![app(le, vec![right, left])]),
                    "gt" => app("not", vec![app(le, vec![left, right])]),
                    _ => return None,
                };
                self.expression(value, None, &[a, b])
            }
            (None, None) if matches!(op, "eq" | "ne") => self.expression(
                app(
                    if op == "eq" { "=" } else { "xor" },
                    vec![reference(a), reference(b)],
                ),
                None,
                &[a, b],
            ),
            _ => None,
        }
    }

    fn term(&mut self, term: &Term, depth: usize) -> Stoppable<Option<usize>> {
        stop::check()?;
        if depth >= DEPTH_LIMIT || *self.remaining == 0 {
            return Ok(None);
        }
        *self.remaining -= 1;
        if let Some(id) = self.memo.get(term) {
            return Ok(Some(*id));
        }
        let result = self.term_node(term, depth)?.or_else(|| {
            // Pure Boolean results are finite inputs even when their source head is
            // not word arithmetic. The whole-plan eligibility check and domain guard
            // retain the same effect/partiality boundary as scalar observations.
            if self.opaque_boolean_inputs && term.sort().is_builtin(BuiltinSort::Bool) {
                self.push(Value::Input(term.clone()), None)
            } else {
                None
            }
        });
        if let Some(id) = result {
            self.memo.insert(term.clone(), id);
        }
        Ok(result)
    }

    fn term_node(&mut self, term: &Term, depth: usize) -> Stoppable<Option<usize>> {
        if let Some(value) = integer(term) {
            let interval = Interval::literal(value.clone());
            return Ok(interval
                .width()
                .and_then(|width| self.expression(literal(&value, width), Some(interval), &[])));
        }
        if let Some(value) = read_bool(term) {
            return Ok(self.expression(atom(value), None, &[]));
        }
        // A bounded scalar observation is an input value just as a scalar variable is.
        // Its range and original domain are checked again by the emitted plan guard;
        // neither the hint nor a facade result sort asserts global definedness.
        if term.sort().is_builtin(BuiltinSort::Int)
            && let Some(interval) = self.bounds.get(term).cloned()
        {
            self.plan.used.insert(term.clone(), interval.clone());
            return Ok(self.push(Value::Input(term.clone()), Some(interval)));
        }
        match term.kind() {
            TermKind::Variable(variable) if variable.kind == VariableKind::Element => {
                let interval = if term.sort().is_builtin(BuiltinSort::Int) {
                    let Some(interval) = self.bounds.get(term).cloned() else {
                        return Ok(None);
                    };
                    self.plan.used.insert(term.clone(), interval.clone());
                    Some(interval)
                } else if term.sort().is_builtin(BuiltinSort::Bool) {
                    None
                } else {
                    return Ok(None);
                };
                Ok(self.push(Value::Input(term.clone()), interval))
            }
            TermKind::Application {
                symbol, arguments, ..
            } => {
                let Some(hook) = symbol.attributes.hook.as_deref() else {
                    return self.helper(term, depth);
                };
                // Arity and carrier checks precede interpreting any hook.
                let int_result = term.sort().is_builtin(BuiltinSort::Int);
                let bool_result = term.sort().is_builtin(BuiltinSort::Bool);
                let all_int = arguments
                    .iter()
                    .all(|a| a.sort().is_builtin(BuiltinSort::Int));
                let all_bool = arguments
                    .iter()
                    .all(|a| a.sort().is_builtin(BuiltinSort::Bool));
                let typed = match (hook, arguments.as_slice()) {
                    ("KEQUAL.ite", [test, yes, no]) => {
                        test.sort().is_builtin(BuiltinSort::Bool)
                            && yes.sort() == no.sort()
                            && yes.sort() == term.sort()
                            && (int_result || bool_result)
                    }
                    ("BOOL.not", [_]) => bool_result && all_bool,
                    (
                        "BOOL.and" | "BOOL.or" | "BOOL.andThen" | "BOOL.orElse" | "BOOL.xor"
                        | "BOOL.eq" | "BOOL.ne" | "BOOL.implies",
                        [_, _],
                    ) => bool_result && all_bool,
                    ("INT.eq" | "INT.ne" | "INT.lt" | "INT.le" | "INT.gt" | "INT.ge", [_, _]) => {
                        bool_result && all_int
                    }
                    (
                        "INT.add" | "INT.sub" | "INT.mul" | "INT.and" | "INT.or" | "INT.xor"
                        | "INT.shl" | "INT.shr" | "INT.ediv" | "INT.emod" | "INT.tdiv" | "INT.tmod",
                        [_, _],
                    ) => int_result && all_int,
                    ("INT.bitRange", [_, _, _]) => int_result && all_int,
                    _ => false,
                };
                if !typed {
                    return Ok(None);
                }
                if matches!(hook, "INT.and" | "INT.or" | "INT.xor") {
                    // The retained exact literal reader can emit a mask run per pair of bits.
                    // Charge that additional work before constructing its scalar fallback.
                    let cost = arguments
                        .iter()
                        .filter_map(integer)
                        .map(|n| n.bits() as usize * 8)
                        .sum();
                    let Some(remaining) = self.remaining.checked_sub(cost) else {
                        return Ok(None);
                    };
                    *self.remaining = remaining;
                }
                let mut ids = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    let Some(id) = self.term(argument, depth + 1)? else {
                        return Ok(None);
                    };
                    ids.push(id);
                }
                Ok(self.operation(hook, arguments, &ids))
            }
            TermKind::And(..)
            | TermKind::DomainValue { .. }
            | TermKind::Variable(_)
            | TermKind::Injection { .. }
            | TermKind::Map { .. }
            | TermKind::List { .. }
            | TermKind::Set { .. } => Ok(None),
        }
    }

    fn operation(&mut self, hook: &str, args: &[Term], ids: &[usize]) -> Option<usize> {
        let a = ids[0];
        if hook == "BOOL.not" {
            return self.expression(app("not", vec![reference(a)]), None, &[a]);
        }
        let b = ids[1];
        if let Some(op) = hook.strip_prefix("BOOL.") {
            let op = match op {
                "eq" => "=",
                "ne" | "xor" => "xor",
                // `=>` is not internalized as written ([`internalized_operators`]).
                "implies" => {
                    let value = app("or", vec![app("not", vec![reference(a)]), reference(b)]);
                    return self.expression(value, None, &[a, b]);
                }
                "and" | "andThen" => "and",
                "or" | "orElse" => "or",
                _ => return None,
            };
            return self.expression(app(op, vec![reference(a), reference(b)]), None, &[a, b]);
        }
        if hook == "KEQUAL.ite" {
            return self.conditional(a, b, ids[2]);
        }
        let op = hook.strip_prefix("INT.")?;
        if matches!(op, "eq" | "ne" | "lt" | "le" | "gt" | "ge") {
            return self.comparison(op, a, b);
        }
        let x = self.range(a)?.clone();
        let y = self.range(b)?.clone();
        let (operator, interval) = match op {
            "add" => (
                "bvadd",
                Interval {
                    lo: &x.lo + &y.lo,
                    hi: &x.hi + &y.hi,
                },
            ),
            "sub" => (
                "bvsub",
                Interval {
                    lo: &x.lo - &y.hi,
                    hi: &x.hi - &y.lo,
                },
            ),
            "mul" => {
                let products = [&x.lo * &y.lo, &x.lo * &y.hi, &x.hi * &y.lo, &x.hi * &y.hi];
                (
                    "bvmul",
                    Interval {
                        lo: products.iter().min()?.clone(),
                        hi: products.iter().max()?.clone(),
                    },
                )
            }
            "and" | "or" | "xor" => {
                self.plan.interesting |= integer(&args[0]).is_none() && integer(&args[1]).is_none();
                let domain = x.union(&y);
                let width = domain.width()?;
                let nonnegative_mask = if op == "and" {
                    [x.clone(), y.clone()]
                        .into_iter()
                        .filter(|r| !r.signed())
                        .map(|r| r.hi)
                        .min()
                } else {
                    None
                };
                let interval = if let Some(hi) = nonnegative_mask {
                    Interval {
                        lo: BigInt::zero(),
                        hi,
                    }
                } else if domain.signed() {
                    let half = BigInt::one() << (width - 1);
                    Interval {
                        lo: -&half,
                        hi: half - 1,
                    }
                } else {
                    Interval::unsigned(width)
                };
                let operator = match op {
                    "and" => "bvand",
                    "or" => "bvor",
                    _ => "bvxor",
                };
                (operator, interval)
            }
            "shl" | "shr" | "ediv" | "emod" | "tdiv" | "tmod" | "bitRange" => {
                return self.projection(op, args, a, &x);
            }
            _ => return None,
        };
        let width = interval.width()?;
        let value = app(
            operator,
            vec![self.resize(a, width)?, self.resize(b, width)?],
        );
        self.expression(value, Some(interval), &[a, b])
    }

    fn projection(&mut self, op: &str, args: &[Term], a: usize, x: &Interval) -> Option<usize> {
        let amount = if matches!(op, "ediv" | "emod" | "tdiv" | "tmod") {
            let divisor = integer(&args[1])?;
            if divisor <= BigInt::zero() || divisor.bits() > u64::from(WIDTH_LIMIT) {
                return None;
            }
            let exponent = u32::try_from(divisor.bits() - 1).ok()?;
            if divisor != BigInt::one() << exponent {
                return None;
            }
            exponent
        } else {
            u32::try_from(integer(&args[1])?)
                .ok()
                .filter(|n| *n <= WIDTH_LIMIT)?
        };

        if matches!(op, "tdiv" | "tmod") && x.signed() {
            // Compiled Euclidean division uses toward-zero division internally. A signed
            // numerator cannot use an arithmetic shift alone for toward-zero division
            // (`signed_power_division`).
            let divisor = BigInt::one() << amount;
            let interval = if op == "tdiv" {
                Interval {
                    lo: &x.lo / &divisor,
                    hi: &x.hi / &divisor,
                }
            } else {
                let maximum: BigInt = &divisor - 1;
                Interval {
                    lo: x.lo.clone().max(-&maximum),
                    hi: x.hi.clone().max(BigInt::zero()).min(maximum),
                }
            };
            let result_width = interval.width()?;
            // Include a sign bit for the positive divisor, in addition to its highest set bit.
            let width = x.width()?.max(amount + 2).max(result_width);
            if width > WIDTH_LIMIT {
                return None;
            }
            let mut value =
                signed_power_division(op == "tmod", self.resize(a, width)?, amount, width);
            if result_width < width {
                value = app(format!("(_ extract {} 0)", result_width - 1), vec![value]);
            }
            return self.expression(value, Some(interval), &[a]);
        }
        if op == "shl" {
            let interval = Interval {
                lo: &x.lo << amount,
                hi: &x.hi << amount,
            };
            let width = interval.width()?;
            return self.expression(
                app(
                    "bvshl",
                    vec![
                        self.resize(a, width)?,
                        literal(&BigInt::from(amount), width),
                    ],
                ),
                Some(interval),
                &[a],
            );
        }
        let length = if op == "bitRange" {
            Some(
                u32::try_from(integer(&args[2])?)
                    .ok()
                    .filter(|n| *n <= WIDTH_LIMIT)?,
            )
        } else if matches!(op, "emod" | "tmod") {
            Some(amount)
        } else {
            None
        };
        let shift = if matches!(op, "emod" | "tmod") {
            0
        } else {
            amount
        };
        let interval = if let Some(length) = length {
            Interval::unsigned(length)
        } else {
            Interval {
                lo: &x.lo >> shift,
                hi: &x.hi >> shift,
            }
        };
        let result_width = interval.width()?;
        // Preserve sign while shifting; include the count itself so it cannot wrap to zero.
        let width = x
            .width()?
            .max(result_width)
            .max(32 - shift.leading_zeros())
            .max(1);
        if width > WIDTH_LIMIT {
            return None;
        }
        let mut value = self.resize(a, width)?;
        if shift != 0 {
            value = app(
                if x.signed() { "bvashr" } else { "bvlshr" },
                vec![value, literal(&BigInt::from(shift), width)],
            );
        }
        if let Some(length) = length {
            value = app(
                "bvand",
                vec![value, literal(&((BigInt::one() << length) - 1), width)],
            );
        }
        if result_width < width {
            value = app(format!("(_ extract {} 0)", result_width - 1), vec![value]);
        }
        self.expression(value, Some(interval), &[a])
    }
}

/// The quotient, or with `remainder` the remainder, of the signed `width`-bit value `x` divided
/// by `2^amount` toward zero, with `width >= amount + 2`, in operators Z3's search internalizes
/// as written ([`internalized_operators`]; neither `bvsdiv` nor `bvsrem` is one).
///
/// An arithmetic shift right by `amount` divides by `2^amount` rounding down, which is toward
/// zero for `x >= 0`. For `x < 0`, toward zero is rounding up, and `ceil(x / 2^k)` is
/// `floor((x + 2^k - 1) / 2^k)`; the sum does not wrap, as `x + 2^k - 1 <= 2^k - 2`, which is
/// below `2^(width - 1)` when `width >= k + 2`. The remainder is `x - (x / 2^k) * 2^k`: the
/// product's magnitude is at most `|x|` and the remainder's below `2^k`, so neither wraps.
fn signed_power_division(remainder: bool, x: SExpr, amount: u32, width: u32) -> SExpr {
    let zero = literal(&BigInt::zero(), width);
    let bias = app(
        "ite",
        vec![
            app("bvsle", vec![zero.clone(), x.clone()]),
            zero,
            literal(&((BigInt::one() << amount) - 1), width),
        ],
    );
    let amount = literal(&BigInt::from(amount), width);
    let quotient = app(
        "bvashr",
        vec![app("bvadd", vec![x.clone(), bias]), amount.clone()],
    );
    if remainder {
        app("bvsub", vec![x, app("bvshl", vec![quotient, amount])])
    } else {
        quotient
    }
}

impl Plan {
    fn emit(
        self,
        state: &mut TranslationState,
        fallback: SExpr,
    ) -> Stoppable<Result<SExpr, TranslationError>> {
        let mut guard = Vec::new();
        let mut guarded = BTreeSet::new();
        for node in &self.nodes {
            if let Value::Input(term) = &node.value
                && !term.attributes().ceil_free()
                && guarded.insert(term.clone())
            {
                let domain = match state.translate_predicate(&Predicate::Ceil(term.clone())) {
                    Ok(domain) => domain,
                    Err(error) => return Ok(Err(error)),
                };
                guard.push(domain);
            }
        }
        for (term, range) in &self.used {
            stop::check()?;
            let input = match state.translate_term(term) {
                Ok(input) => input,
                Err(error) => return Ok(Err(error)),
            };
            guard.push(app("<=", vec![atom(&range.lo), input.clone()]));
            guard.push(app("<=", vec![input, atom(&range.hi)]));
        }
        let body = match emit_nodes(self.nodes, self.root, state)? {
            Ok(body) => body,
            Err(error) => return Ok(Err(error)),
        };
        let guard = if guard.is_empty() {
            atom(true)
        } else {
            app("and", guard)
        };
        Ok(Ok(app("ite", vec![guard, body, fallback])))
    }
}

fn emit_nodes(
    nodes: Vec<Node>,
    root: usize,
    state: &mut TranslationState,
) -> Stoppable<Result<SExpr, TranslationError>> {
    let mut body = reference(root);
    let mut bindings: BTreeMap<usize, Vec<SExpr>> = BTreeMap::new();
    for (id, node) in nodes.into_iter().enumerate() {
        stop::check()?;
        let value = match node.value {
            Value::Expression(value) => value,
            Value::Parameter(name) => atom(name),
            Value::Input(term) => {
                let input = match state.translate_term(&term) {
                    Ok(input) => input,
                    Err(error) => return Ok(Err(error)),
                };
                match node.interval {
                    Some(range) => app(
                        format!("(_ int2bv {})", range.width().expect("checked plan width")),
                        vec![input],
                    ),
                    None => input,
                }
            }
        };
        bindings
            .entry(node.level)
            .or_default()
            .push(SExpr::List(vec![reference(id), value]));
    }
    for (_, bindings) in bindings.into_iter().rev() {
        stop::check()?;
        body = app("let", vec![SExpr::List(bindings), body]);
    }
    Ok(Ok(body))
}

/// Group independent scalar bindings too, keeping let depth proportional to source depth.
/// Values mention preceding fresh bindings; scanning each value accounts for literal-reader
/// templates without expanding any referenced value.
pub(super) fn scalar_bindings(bindings: Vec<(String, SExpr)>, mut body: SExpr) -> Stoppable<SExpr> {
    let mut levels = FxHashMap::default();
    let mut groups: BTreeMap<usize, Vec<SExpr>> = BTreeMap::new();
    for (name, value) in bindings {
        let mut level = 0;
        let mut pending = vec![&value];
        while let Some(expression) = pending.pop() {
            stop::check()?;
            match expression {
                SExpr::Atom(name) => {
                    if let Some(dependency) = levels.get(name) {
                        level = level.max(dependency + 1);
                    }
                }
                SExpr::List(children) => pending.extend(children),
            }
        }
        levels.insert(name.clone(), level);
        groups
            .entry(level)
            .or_default()
            .push(SExpr::List(vec![atom(name), value]));
    }
    for (_, bindings) in groups.into_iter().rev() {
        stop::check()?;
        body = app("let", vec![SExpr::List(bindings), body]);
    }
    Ok(body)
}

/// Count the exact Display byte length before allocating/expanding the script text.
pub(super) fn fits_text(expression: &SExpr, remaining: &mut usize) -> Stoppable<bool> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        stop::check()?;
        let cost = match expression {
            SExpr::Atom(text) => text.len(),
            SExpr::List(children) => {
                pending.extend(children);
                2 + children.len().saturating_sub(1)
            }
        };
        let Some(rest) = remaining.checked_sub(cost) else {
            return Ok(false);
        };
        *remaining = rest;
    }
    Ok(true)
}

// Only unconditional conjuncts contribute hints. Even these hints are restated exactly in each
// plan's guard; they are neither global domain evidence nor source-summary metadata.
fn bounds(known: &[Predicate], remaining: &mut usize) -> Stoppable<BTreeMap<Term, Interval>> {
    let mut limits: BTreeMap<Term, (Option<BigInt>, Option<BigInt>)> = BTreeMap::new();
    let mut pending = known.iter().take(*remaining).collect::<Vec<_>>();
    while let Some(predicate) = pending.pop() {
        stop::check()?;
        if *remaining == 0 {
            break;
        }
        *remaining -= 1;
        let test = match predicate {
            Predicate::And(children) => {
                pending.extend(
                    children
                        .iter()
                        .take(remaining.saturating_sub(pending.len())),
                );
                continue;
            }
            Predicate::Term(term) => Some((term, true)),
            Predicate::Equals(a, b) => read_bool(b)
                .map(|truth| (a, truth))
                .or_else(|| read_bool(a).map(|truth| (b, truth))),
            Predicate::True
            | Predicate::False
            | Predicate::Ceil(_)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Not(_)
            | Predicate::Or(_)
            | Predicate::Implies(..)
            | Predicate::Iff(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_)
            | Predicate::Defined(_) => None,
        };
        let Some((term, truth)) = test else {
            continue;
        };
        let TermKind::Application {
            symbol, arguments, ..
        } = term.kind()
        else {
            continue;
        };
        let [a, b] = arguments.as_slice() else {
            continue;
        };
        if !term.sort().is_builtin(BuiltinSort::Bool)
            || !a.sort().is_builtin(BuiltinSort::Int)
            || !b.sort().is_builtin(BuiltinSort::Int)
        {
            continue;
        }
        let hook = symbol.attributes.hook.as_deref();
        let (var, value, lower, strict) = match (hook, integer(a), integer(b)) {
            (Some("INT.lt"), None, Some(n)) => (a, n, !truth, truth),
            (Some("INT.le"), None, Some(n)) => (a, n, !truth, !truth),
            (Some("INT.gt"), None, Some(n)) => (a, n, truth, truth),
            (Some("INT.ge"), None, Some(n)) => (a, n, truth, !truth),
            (Some("INT.lt"), Some(n), None) => (b, n, truth, truth),
            (Some("INT.le"), Some(n), None) => (b, n, truth, !truth),
            (Some("INT.gt"), Some(n), None) => (b, n, !truth, truth),
            (Some("INT.ge"), Some(n), None) => (b, n, !truth, !truth),
            _ => continue,
        };
        if value.bits() > u64::from(WIDTH_LIMIT) {
            continue;
        }
        let value = if strict {
            if lower { value + 1 } else { value - 1 }
        } else {
            value
        };
        let (lo, hi) = limits.entry(var.clone()).or_default();
        if lower {
            *lo = Some(lo.take().map_or(value.clone(), |old| old.max(value)));
        } else {
            *hi = Some(hi.take().map_or(value.clone(), |old| old.min(value)));
        }
    }
    Ok(limits
        .into_iter()
        .filter_map(|(term, (lo, hi))| {
            let range = Interval { lo: lo?, hi: hi? };
            range.width().map(|_| (term, range))
        })
        .collect())
}

/// A source observation can suggest the bounded region of an observed operand.
/// These are hints only: the plan checks that operand's actual range and domain.
/// A conditional with an unbounded/absent branch may suggest its other branch's range;
/// the word reading is then used only where the guarded region actually holds.
fn observation_hints(
    state: &TranslationState,
    bounds: &mut BTreeMap<Term, Interval>,
    remaining: &mut usize,
) -> Stoppable<()> {
    use crate::observation::reading::Reading;
    fn hint(
        value: &Arc<Reading>,
        state: &TranslationState,
        bounds: &BTreeMap<Term, Interval>,
        active: &mut BTreeSet<Term>,
        memo: &mut BTreeMap<usize, Option<Interval>>,
        remaining: &mut usize,
        depth: usize,
    ) -> Stoppable<Option<Interval>> {
        stop::check()?;
        if *remaining == 0 || depth >= DEPTH_LIMIT {
            return Ok(None);
        }
        let key = Arc::as_ptr(value) as usize;
        if let Some(hint) = memo.get(&key) {
            return Ok(hint.clone());
        }
        *remaining -= 1;
        let found = match value.as_ref() {
            Reading::Missing => None,
            Reading::Leaf(term) => {
                if let Some(range) = bounds.get(term) {
                    Some(range.clone())
                } else if let Some(value) = integer(term) {
                    Some(Interval::literal(value))
                } else if active.insert(term.clone()) {
                    let found = if let Some(reading) = state.observations.get(term) {
                        hint(reading, state, bounds, active, memo, remaining, depth + 1)?
                    } else {
                        None
                    };
                    active.remove(term);
                    found
                } else {
                    None
                }
            }
            Reading::If { yes, no, .. } => {
                match (
                    hint(yes, state, bounds, active, memo, remaining, depth + 1)?,
                    hint(no, state, bounds, active, memo, remaining, depth + 1)?,
                ) {
                    (Some(a), Some(b)) => Some(a.union(&b)),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                }
            }
        }
        .filter(|range| range.width().is_some());
        memo.insert(key, found.clone());
        Ok(found)
    }
    let mut active = BTreeSet::new();
    let mut memo = BTreeMap::new();
    for (term, reading) in &state.observations {
        stop::check()?;
        if *remaining == 0 {
            break;
        }
        if !term.sort().is_builtin(BuiltinSort::Int) || bounds.contains_key(term) {
            continue;
        }
        active.insert(term.clone());
        let found = hint(reading, state, bounds, &mut active, &mut memo, remaining, 0)?;
        active.remove(term);
        if let Some(range) = found {
            bounds.insert(term.clone(), range);
        }
    }
    Ok(())
}

/// Definition-aware query preparation. No bound occurrence is lifted out of its binder.
pub(super) fn prepare(
    state: &mut TranslationState,
    known: &[Predicate],
    checked: &[Predicate],
) -> Stoppable<Result<(), TranslationError>> {
    stop::check()?;
    if state.congruence.is_none() {
        return Ok(Ok(()));
    }
    let mut remaining = WORK_LIMIT;
    let mut text_remaining = TEXT_LIMIT;
    let mut registry = Registry::new(state.summaries.clone());
    let mut bounds = bounds(known, &mut remaining)?;
    observation_hints(state, &mut bounds, &mut remaining)?;
    let demands = state.word_demands.iter().cloned().collect::<Vec<_>>();
    if known
        .len()
        .saturating_add(checked.len())
        .saturating_add(demands.len())
        > remaining
    {
        return Ok(Ok(()));
    }
    let mut pending = known
        .iter()
        .chain(checked)
        .chain(&demands)
        .take(remaining)
        .collect::<Vec<_>>();
    let mut source_facts = Vec::new();
    while let Some(predicate) = pending.pop() {
        stop::check()?;
        if remaining == 0 {
            // Unvisited occurrences might duplicate a prepared expression. Without counting
            // them the output budget would not bound the text actually emitted.
            state.word_predicates.clear();
            return Ok(Ok(()));
        }
        remaining -= 1;
        match predicate {
            Predicate::And(children) | Predicate::Or(children) => {
                if children.len() > remaining.saturating_sub(pending.len()) {
                    state.word_predicates.clear();
                    return Ok(Ok(()));
                }
                pending.extend(
                    children
                        .iter()
                        .take(remaining.saturating_sub(pending.len())),
                );
                continue;
            }
            Predicate::Not(child) => {
                pending.push(child);
                continue;
            }
            Predicate::Implies(a, b) | Predicate::Iff(a, b) => {
                if remaining.saturating_sub(pending.len()) < 2 {
                    state.word_predicates.clear();
                    return Ok(Ok(()));
                }
                pending.extend(
                    [a.as_ref(), b.as_ref()]
                        .into_iter()
                        .take(remaining.saturating_sub(pending.len())),
                );
                continue;
            }
            Predicate::Term(_) | Predicate::Equals(..) => {}
            Predicate::True
            | Predicate::False
            | Predicate::Ceil(_)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_)
            | Predicate::Defined(_) => continue,
        }
        if let Some(value) = state.word_predicates.get(predicate) {
            if !fits_text(value, &mut text_remaining)? {
                state.word_predicates.clear();
                return Ok(Ok(()));
            }
            continue;
        }
        let terms: Vec<&Term> = match predicate {
            Predicate::Term(t) => vec![t],
            Predicate::Equals(a, b) => vec![a, b],
            Predicate::True
            | Predicate::False
            | Predicate::Ceil(_)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Not(_)
            | Predicate::Or(_)
            | Predicate::Implies(..)
            | Predicate::Iff(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_)
            | Predicate::Defined(_)
            | Predicate::And(_) => unreachable!(),
        };
        let mut planner = Planner {
            bounds: &bounds,
            registry: Some(&mut registry),
            opaque_boolean_inputs: true,
            remaining: &mut remaining,
            memo: FxHashMap::default(),
            decisions: FxHashMap::default(),
            plan: Plan {
                nodes: Vec::new(),
                used: BTreeMap::new(),
                root: 0,
                interesting: false,
            },
        };
        let root = match predicate {
            Predicate::Term(term) if term.sort().is_builtin(BuiltinSort::Bool) => {
                planner.term(term, 0)?
            }
            Predicate::Equals(a, b) => match (planner.term(a, 0)?, planner.term(b, 0)?) {
                (Some(a), Some(b)) => planner.comparison("eq", a, b),
                _ => None,
            },
            Predicate::True
            | Predicate::False
            | Predicate::Ceil(_)
            | Predicate::Floor(_)
            | Predicate::In(..)
            | Predicate::Not(_)
            | Predicate::Or(_)
            | Predicate::Implies(..)
            | Predicate::Iff(..)
            | Predicate::Exists(..)
            | Predicate::Forall(..)
            | Predicate::Absent(_)
            | Predicate::Defined(_)
            | Predicate::And(_)
            | Predicate::Term(_) => None,
        };
        let Some(root) = root else {
            continue;
        };
        if !planner.plan.interesting || !terms.iter().all(|term| state.eligible_operand(term)) {
            continue;
        }
        planner.plan.root = root;
        stop::check()?;
        // Share the scalar fallback too: retaining it must not expand a source DAG into a tree.
        // Its lets are emitted with the fallback alone, so this must be the only open scope
        // (`prepare` runs at preparation, before any query is translated).
        debug_assert!(
            state.scopes.is_empty(),
            "scalar fallback scope opened inside another scope"
        );
        state.open_scope(None, false, true);
        // The scalar reading alone: the fact below relates the two readings under the
        // operands' domains, and the query states those domains beside the word value where
        // it asserts the predicate (`TranslationState::atom_with_domains`).
        let fallback = state.translate_predicate_reading(predicate);
        let scope = state
            .close_scope(None)
            .terms
            .expect("scalar fallback scope");
        let fallback = match fallback {
            Ok(value) => value,
            Err(error) => return Ok(Err(error)),
        };
        let fallback = scalar_bindings(scope.bindings, fallback)?;
        let emitted = planner.plan.emit(state, fallback.clone())?;
        match emitted {
            Ok(value) => {
                if fits_text(&value, &mut text_remaining)? {
                    let domain = match state.translate_predicate(&Predicate::And(
                        terms
                            .iter()
                            .map(|t| Predicate::Ceil((*t).clone()))
                            .collect::<Vec<_>>()
                            .into(),
                    )) {
                        Ok(domain) => domain,
                        Err(error) => return Ok(Err(error)),
                    };
                    let fact = app("=>", vec![domain, app("=", vec![fallback, value.clone()])]);
                    if !fits_text(&fact, &mut text_remaining)? {
                        state.word_predicates.clear();
                        return Ok(Ok(()));
                    }
                    source_facts.push(fact);
                    state.word_predicates.insert(predicate.clone(), value);
                }
            }
            Err(error) => return Ok(Err(error)),
        }
    }
    match registry.emit(state, &mut text_remaining)? {
        Ok(true) => {
            for fact in source_facts {
                stop::check()?;
                if let Err(error) = state.record_source_fact(fact) {
                    return Ok(Err(error));
                }
            }
        }
        Ok(false) => state.word_predicates.clear(),
        Err(error) => return Ok(Err(error)),
    }
    Ok(Ok(()))
}
