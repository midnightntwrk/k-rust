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
            // As for scalar definitions, retain applications during parsing instead of
            // eagerly macro-expanding distinct-argument dependency diamonds.
            let expression = app(
                "define-fun-rec",
                vec![
                    atom(definition.name),
                    SExpr::List(parameters),
                    atom(sort(result)),
                    body,
                ],
            );
            if !fits_text(&expression, text)? {
                return Ok(Ok(false));
            }
            state.derived_definitions.push(expression.to_string());
        }
        Ok(Ok(true))
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

    fn comparison(&mut self, op: &str, a: usize, b: usize) -> Option<usize> {
        match (self.range(a), self.range(b)) {
            (Some(a_range), Some(b_range)) => {
                let combined = a_range.union(b_range);
                let width = combined.width()?;
                let operator = match op {
                    "eq" | "ne" => "=",
                    "lt" => {
                        if combined.signed() {
                            "bvslt"
                        } else {
                            "bvult"
                        }
                    }
                    "le" => {
                        if combined.signed() {
                            "bvsle"
                        } else {
                            "bvule"
                        }
                    }
                    "gt" => {
                        if combined.signed() {
                            "bvsgt"
                        } else {
                            "bvugt"
                        }
                    }
                    "ge" => {
                        if combined.signed() {
                            "bvsge"
                        } else {
                            "bvuge"
                        }
                    }
                    _ => return None,
                };
                let result = app(
                    operator,
                    vec![self.resize(a, width)?, self.resize(b, width)?],
                );
                self.expression(
                    if op == "ne" {
                        app("not", vec![result])
                    } else {
                        result
                    },
                    None,
                    &[a, b],
                )
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
        let result = self.term_node(term, depth)?;
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
                "implies" => "=>",
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
            // numerator cannot use an arithmetic shift for toward-zero division.
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
            let mut value = app(
                if op == "tdiv" { "bvsdiv" } else { "bvsrem" },
                vec![self.resize(a, width)?, literal(&divisor, width)],
            );
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

impl Plan {
    fn emit(
        self,
        state: &mut TranslationState,
        fallback: SExpr,
    ) -> Stoppable<Result<SExpr, TranslationError>> {
        let mut guard = Vec::new();
        for (term, range) in &self.used {
            stop::check()?;
            let input = match state.translate_term(term) {
                Ok(input) => input,
                Err(error) => return Ok(Err(error)),
            };
            if !term.attributes().ceil_free() {
                let domain = match state.translate_predicate(&Predicate::Ceil(term.clone())) {
                    Ok(domain) => domain,
                    Err(error) => return Ok(Err(error)),
                };
                guard.push(domain);
            }
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
    if known.len().saturating_add(checked.len()) > remaining {
        return Ok(Ok(()));
    }
    let mut pending = known
        .iter()
        .chain(checked)
        .take(remaining)
        .collect::<Vec<_>>();
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
        state.shared_terms = Some(super::SharedTerms::default());
        let fallback = state.translate_predicate(predicate);
        let scope = state.shared_terms.take().expect("scalar fallback scope");
        let fallback = match fallback {
            Ok(value) => value,
            Err(error) => return Ok(Err(error)),
        };
        let fallback = scalar_bindings(scope.bindings, fallback)?;
        let emitted = planner.plan.emit(state, fallback)?;
        match emitted {
            Ok(value) => {
                if fits_text(&value, &mut text_remaining)? {
                    state.word_predicates.insert(predicate.clone(), value);
                }
            }
            Err(error) => return Ok(Err(error)),
        }
    }
    match registry.emit(state, &mut text_remaining)? {
        Ok(true) => {}
        Ok(false) => state.word_predicates.clear(),
        Err(error) => return Ok(Err(error)),
    }
    Ok(Ok(()))
}
