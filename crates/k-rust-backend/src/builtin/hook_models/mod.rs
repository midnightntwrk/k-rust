//! Model-based tests of the `LIST`, `MAP`, `SET`, `BYTES`, `STRING` and `FLOAT` hooks.
//!
//! Each hook is checked against a model written from its documented meaning
//! (`crates/k-rust/builtin/domains.md`): `Vec` for lists, `BTreeMap` and `BTreeSet` for maps and
//! sets, byte vectors for `Bytes`, code-point sequences for `String`, and exact rational
//! arithmetic rounded to the IEEE formats for `Float`. A case is a hook applied to arguments that
//! may contain variables: element variables, opaque list, map and set segments, and opaque
//! scalar arguments. Every case carries an assignment of values to its variables, and is checked
//! on that instance:
//!
//! - the arguments are instantiated and evaluated; on these concrete arguments the hook must
//!   return the model's value, or `\bottom` where the model is undefined (the hook may decline
//!   only where its documentation leaves the answer open);
//! - the hook is also evaluated on the symbolic arguments. A value is sound only if, under the
//!   assignment, it denotes the concrete result, and `\bottom` only if the concrete result is
//!   undefined. Declining is always sound.
//!
//! A hooked application is strict, so an assignment under which an argument is itself undefined
//! (a map binding a key twice, a set holding an element twice) says nothing about the hook and is
//! skipped.

mod collections;
mod float;
mod scalars;

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    fmt::Write as _,
    sync::Arc,
};

use num_bigint::BigInt;
use proptest::{
    collection::vec,
    prelude::any,
    test_runner::{Config, RngAlgorithm, TestCaseError, TestRng, TestRunner},
};

use k_rust_kore::names::BuiltinSort;

use super::{BuiltinResult, UnsupportedHookReason, evaluate_hook_into};
use crate::term::{
    CollectionMetadata, CollectionSymbols, ListDefinition, MapDefinition, SetDefinition, Sort,
    Symbol, Term, TermKind, Variable,
};

/// A value of the models. Floats are kept as their format and bit pattern, with every NaN
/// collapsed to one, because a `Float` token denotes no NaN payload.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum Val {
    Bool(bool),
    Int(BigInt),
    Str(Vec<u8>),
    Bytes(Vec<u8>),
    Float(float::Format, u64),
    Item(u8),
    /// A nullary constructor (`LE`, `Signed`, ...), by its KORE symbol name.
    Tag(String),
    /// A token of a user sort, by sort name and text.
    Token(String, Vec<u8>),
    List(Vec<Val>),
    Set(BTreeSet<Val>),
    Map(BTreeMap<Val, Val>),
}

impl Val {
    pub(super) fn int(value: impl Into<BigInt>) -> Self {
        Self::Int(value.into())
    }
}

/// What the documentation says a hook returns on concrete arguments.
#[derive(Clone, Debug)]
pub(super) enum Expect {
    Value(Val),
    Bottom,
    /// Any one of these values (the documentation leaves the choice to the backend).
    OneOf(Vec<Val>),
    /// A list holding exactly these values in some order (the order is the backend's choice,
    /// but it must be a function of the argument values, which the instance check enforces).
    Permutation(Vec<Val>),
    /// The documentation does not determine the result; any answer is accepted, and the
    /// symbolic evaluation must still agree with the concrete one.
    Open,
    /// The hook is `total` and its documentation gives no value here: the hook must leave the
    /// application unevaluated as `Unspecified`, and no symbolic evaluation may decide it.
    Unspecified,
}

/// A model's verdict: the expected result, and whether the hook may decline these concrete
/// arguments (return `NotApplicable` or `Unsupported`) without being incomplete.
#[derive(Clone, Debug)]
pub(super) struct Spec {
    pub(super) expect: Expect,
    pub(super) may_decline: bool,
}

impl Spec {
    pub(super) fn value(value: Val) -> Self {
        Self {
            expect: Expect::Value(value),
            may_decline: false,
        }
    }

    pub(super) fn bottom() -> Self {
        Self {
            expect: Expect::Bottom,
            may_decline: false,
        }
    }

    pub(super) fn partial(value: Option<Val>) -> Self {
        value.map_or_else(Self::bottom, Self::value)
    }

    pub(super) fn open() -> Self {
        Self {
            expect: Expect::Open,
            may_decline: true,
        }
    }

    pub(super) fn unspecified() -> Self {
        Self {
            expect: Expect::Unspecified,
            may_decline: true,
        }
    }

    pub(super) fn one_of(values: Vec<Val>) -> Self {
        Self {
            expect: Expect::OneOf(values),
            may_decline: false,
        }
    }

    pub(super) fn permutation(values: Vec<Val>) -> Self {
        Self {
            expect: Expect::Permutation(values),
            may_decline: false,
        }
    }

    pub(super) fn declinable(mut self) -> Self {
        self.may_decline = true;
        self
    }
}

pub(super) type Env = BTreeMap<String, Val>;

/// One hook application and the instance it is checked on.
#[derive(Clone, Debug)]
pub(super) struct Case {
    pub(super) hook: &'static str,
    pub(super) arguments: Vec<Term>,
    pub(super) env: Env,
}

// ---------------------------------------------------------------------------------------------
// Terms of the models' values.

/// The list, set and map sorts the collection hooks are applied in. A hook builds its result in
/// the collection its symbol declares, so the models hold for any names of these sorts and of
/// their unit, element and concatenation symbols; the collection models run once with the
/// builtin sorts' names and once with others.
#[derive(Clone, Debug)]
pub(super) struct Shapes {
    list: Arc<ListDefinition>,
    set: Arc<SetDefinition>,
    map: Arc<MapDefinition>,
}

impl Shapes {
    /// The builtin `List`, `Set` and `Map` sorts' names, holding `SortItem` elements.
    pub(super) fn builtin() -> Self {
        Self::named(
            [
                BuiltinSort::List.kore_name(),
                "Lbl'Stop'List",
                "LblListItem",
                "Lbl'Unds'List'Unds'",
            ],
            [
                BuiltinSort::Set.kore_name(),
                "Lbl'Stop'Set",
                "LblSetItem",
                "Lbl'Unds'Set'Unds'",
            ],
            [
                BuiltinSort::Map.kore_name(),
                "Lbl'Stop'Map",
                "Lbl'UndsPipe'-'-GT-Unds'",
                "Lbl'Unds'Map'Unds'",
            ],
        )
    }

    /// Other sort and symbol names for the same three collections.
    pub(super) fn renamed() -> Self {
        Self::named(
            ["SortItems", "dotItems", "itemsItem", "itemsConcat"],
            ["SortItemSet", "dotItemSet", "itemSetItem", "itemSetConcat"],
            ["SortItemMap", "dotItemMap", "itemMapItem", "itemMapConcat"],
        )
    }

    fn named(list: [&str; 4], set: [&str; 4], map: [&str; 4]) -> Self {
        let symbols = |[_, unit, element, concat]: [&str; 4]| CollectionSymbols {
            unit: unit.into(),
            element: element.into(),
            concat: concat.into(),
        };
        let element_sort = || Sort::simple(item_sort_name());
        Self {
            list: Arc::new(ListDefinition {
                symbols: symbols(list),
                element_sort: element_sort(),
                list_sort: list[0].into(),
            }),
            set: Arc::new(SetDefinition {
                symbols: symbols(set),
                element_sort: element_sort(),
                list_sort: set[0].into(),
            }),
            map: Arc::new(MapDefinition {
                symbols: symbols(map),
                key_sort: element_sort(),
                value_sort: element_sort(),
                map_sort: map[0].into(),
            }),
        }
    }
}

thread_local! {
    static SHAPES: RefCell<Shapes> = RefCell::new(Shapes::builtin());
}

/// Run `body` with the collection hooks applied in `shapes`.
pub(super) fn with_shapes<R>(shapes: Shapes, body: impl FnOnce() -> R) -> R {
    let previous = SHAPES.with(|current| current.replace(shapes));
    let result = body();
    SHAPES.with(|current| current.replace(previous));
    result
}

fn item_sort_name() -> &'static str {
    "SortItem"
}

pub(super) fn item_sort() -> Sort {
    Sort::simple(item_sort_name())
}

pub(super) fn list_definition() -> Arc<ListDefinition> {
    SHAPES.with(|shapes| shapes.borrow().list.clone())
}

pub(super) fn set_definition() -> Arc<SetDefinition> {
    SHAPES.with(|shapes| shapes.borrow().set.clone())
}

pub(super) fn map_definition() -> Arc<MapDefinition> {
    SHAPES.with(|shapes| shapes.borrow().map.clone())
}

/// The collection a hook's symbol declares its result in, as `domains.md` declares the
/// builtin hooked symbols (`LIST.concat : List List -> List`, `MAP.keys : Map -> Set`, ...);
/// `None` for a hook whose result is no collection.
fn result_collection(hook: &str) -> Option<CollectionMetadata> {
    match hook {
        "LIST.concat" | "LIST.element" | "LIST.unit" | "LIST.make" | "LIST.range"
        | "LIST.update" | "LIST.updateAll" | "SET.set2list" | "MAP.keys_list" | "MAP.values" => {
            Some(CollectionMetadata::List(list_definition()))
        }
        "SET.concat" | "SET.element" | "SET.unit" | "SET.difference" | "SET.intersection"
        | "SET.list2set" | "MAP.keys" => Some(CollectionMetadata::Set(set_definition())),
        "MAP.element" | "MAP.unit" | "MAP.update" | "MAP.updateAll" | "MAP.remove"
        | "MAP.removeAll" | "MAP.concat" => Some(CollectionMetadata::Map(map_definition())),
        _ => None,
    }
}

pub(super) fn item(value: u8) -> Term {
    Term::domain_value(item_sort(), format!("i{value}"))
}

pub(super) fn tag(name: &str, sort: &str) -> Term {
    Term::application(
        Arc::new(Symbol::constructor(name, Vec::new(), Sort::simple(sort))),
        Vec::new(),
        Vec::new(),
    )
}

pub(super) fn variable(name: &str, sort: Sort) -> Term {
    Term::variable(Variable::new(name, sort))
}

/// The canonical term of a value. Floats are written by the float model, which owns the token
/// syntax.
pub(super) fn encode(value: &Val) -> Term {
    match value {
        Val::Bool(value) => Term::domain_value(
            Sort::builtin(BuiltinSort::Bool),
            if *value { "true" } else { "false" },
        ),
        Val::Int(value) => Term::domain_value(Sort::builtin(BuiltinSort::Int), value.to_string()),
        Val::Str(value) => Term::domain_value(Sort::builtin(BuiltinSort::String), value.clone()),
        Val::Bytes(value) => Term::domain_value(Sort::builtin(BuiltinSort::Bytes), value.clone()),
        Val::Float(format, bits) => float::token_term(*format, *bits),
        Val::Item(value) => item(*value),
        Val::Tag(name) => tag(name, "SortTag"),
        Val::Token(sort, text) => Term::domain_value(Sort::simple(sort.as_str()), text.clone()),
        Val::List(values) => {
            Term::list(list_definition(), values.iter().map(encode).collect(), None)
        }
        Val::Set(values) => Term::set(set_definition(), values.iter().map(encode).collect(), None),
        Val::Map(entries) => Term::map(
            map_definition(),
            entries
                .iter()
                .map(|(key, value)| (encode(key), encode(value)))
                .collect(),
            None,
        ),
    }
}

/// The value a term denotes under `env`, or `None` where it is undefined (a collection that
/// repeats a set element or a map key). Panics on a term shape the hooks under test never build.
pub(super) fn decode(term: &Term, env: &Env) -> Option<Val> {
    match term.kind() {
        TermKind::Variable(variable) => Some(
            env.get(variable.name.as_ref())
                .unwrap_or_else(|| panic!("no value for variable {}", variable.name))
                .clone(),
        ),
        TermKind::DomainValue { sort, value } => Some(decode_domain_value(sort, value.as_bytes())),
        TermKind::Application {
            symbol, arguments, ..
        } if arguments.is_empty() => Some(Val::Tag(symbol.name.to_string())),
        TermKind::List { heads, rest, .. } => {
            let mut values = heads
                .iter()
                .map(|head| decode(head, env))
                .collect::<Option<Vec<_>>>()?;
            if let Some((middle, tails)) = rest {
                let Val::List(middle) = decode(middle, env)? else {
                    panic!("the middle of a list is not a list: {middle:?}")
                };
                values.extend(middle);
                for tail in tails {
                    values.push(decode(tail, env)?);
                }
            }
            Some(Val::List(values))
        }
        TermKind::Set { elements, rest, .. } => {
            let mut values = BTreeSet::new();
            for element in elements {
                if !values.insert(decode(element, env)?) {
                    return None;
                }
            }
            if let Some(rest) = rest {
                let Val::Set(rest) = decode(rest, env)? else {
                    panic!("the rest of a set is not a set: {rest:?}")
                };
                for value in rest {
                    if !values.insert(value) {
                        return None;
                    }
                }
            }
            Some(Val::Set(values))
        }
        TermKind::Map { entries, rest, .. } => {
            let mut values = BTreeMap::new();
            for (key, value) in entries {
                if values
                    .insert(decode(key, env)?, decode(value, env)?)
                    .is_some()
                {
                    return None;
                }
            }
            if let Some(rest) = rest {
                let Val::Map(rest) = decode(rest, env)? else {
                    panic!("the rest of a map is not a map: {rest:?}")
                };
                for (key, value) in rest {
                    if values.insert(key, value).is_some() {
                        return None;
                    }
                }
            }
            Some(Val::Map(values))
        }
        _ => panic!("the hook models do not decode {term:?}"),
    }
}

fn decode_domain_value(sort: &Sort, value: &[u8]) -> Val {
    let text = || std::str::from_utf8(value).expect("a textual domain value is UTF-8");
    if sort.is_builtin(BuiltinSort::Bool) {
        match text() {
            "true" => Val::Bool(true),
            "false" => Val::Bool(false),
            other => panic!("not a Bool: {other}"),
        }
    } else if sort.is_builtin(BuiltinSort::Int) {
        Val::Int(text().parse().expect("an Int domain value is decimal"))
    } else if sort.is_builtin(BuiltinSort::String) {
        Val::Str(value.to_vec())
    } else if sort.is_builtin(BuiltinSort::Bytes) {
        Val::Bytes(value.to_vec())
    } else if sort.is_builtin(BuiltinSort::Float) {
        let (format, bits) = float::parse_token(text())
            .unwrap_or_else(|| panic!("{:?} is not in the Float syntax", text()));
        Val::Float(format, bits)
    } else if *sort == item_sort() {
        Val::Item(
            text()
                .strip_prefix('i')
                .and_then(|index| index.parse().ok())
                .expect("an item is written iN"),
        )
    } else {
        let crate::term::Sort::Application { name, .. } = sort else {
            panic!("a token of a sort variable")
        };
        Val::Token(name.to_string(), value.to_vec())
    }
}

/// `term` with every variable replaced by the term of its value; the concrete parts, including
/// the token syntax of their domain values, are kept.
pub(super) fn instantiate(term: &Term, env: &Env) -> Term {
    match term.kind() {
        TermKind::Variable(variable) => encode(&env[variable.name.as_ref()]),
        TermKind::List {
            definition,
            heads,
            rest,
        } => Term::list(
            definition.clone(),
            heads.iter().map(|head| instantiate(head, env)).collect(),
            rest.as_ref().map(|(middle, tails)| {
                (
                    instantiate(middle, env),
                    tails.iter().map(|tail| instantiate(tail, env)).collect(),
                )
            }),
        ),
        TermKind::Set {
            definition,
            elements,
            rest,
        } => Term::set(
            definition.clone(),
            elements
                .iter()
                .map(|element| instantiate(element, env))
                .collect(),
            rest.as_ref().map(|rest| instantiate(rest, env)),
        ),
        TermKind::Map {
            definition,
            entries,
            rest,
        } => Term::map(
            definition.clone(),
            entries
                .iter()
                .map(|(key, value)| (instantiate(key, env), instantiate(value, env)))
                .collect(),
            rest.as_ref().map(|rest| instantiate(rest, env)),
        ),
        _ => term.clone(),
    }
}

// ---------------------------------------------------------------------------------------------
// Drawing cases from a byte string, so that proptest shrinks a failure toward the first choice
// of every decision.

pub(super) struct Draw<'a> {
    bytes: &'a [u8],
    position: usize,
    fresh: usize,
}

impl<'a> Draw<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self {
            bytes,
            position: 0,
            fresh: 0,
        }
    }

    pub(super) fn byte(&mut self) -> u8 {
        let byte = self.bytes.get(self.position).copied().unwrap_or(0);
        self.position += 1;
        byte
    }

    /// A number below `bound` (which is positive).
    pub(super) fn below(&mut self, bound: usize) -> usize {
        if bound <= 256 {
            usize::from(self.byte()) % bound
        } else {
            (usize::from(self.byte()) << 8 | usize::from(self.byte())) % bound
        }
    }

    /// True with probability about `numerator / 8`.
    pub(super) fn chance(&mut self, numerator: u8) -> bool {
        self.byte() % 8 >= 8 - numerator
    }

    pub(super) fn pick<T: Clone>(&mut self, choices: &[T]) -> T {
        choices[self.below(choices.len())].clone()
    }

    pub(super) fn u64(&mut self) -> u64 {
        (0..8).fold(0, |value, _| value << 8 | u64::from(self.byte()))
    }

    pub(super) fn fresh_name(&mut self, prefix: &str) -> String {
        self.fresh += 1;
        format!("{prefix}{}", self.fresh)
    }

    /// The term of a concrete scalar argument, or, sometimes, a fresh variable of `sort` that
    /// the instance assigns this value: a hook must not decide what depends on an argument it
    /// cannot read.
    pub(super) fn scalar(&mut self, value: Term, sort: Sort, env: &mut Env) -> Term {
        if self.chance(1) {
            let name = self.fresh_name("V");
            env.insert(name.clone(), decode(&value, &Env::new()).expect("a scalar"));
            variable(&name, sort)
        } else {
            value
        }
    }

    pub(super) fn int(&mut self, value: impl Into<BigInt>, env: &mut Env) -> Term {
        self.scalar(
            encode(&Val::Int(value.into())),
            Sort::builtin(BuiltinSort::Int),
            env,
        )
    }

    /// An index-like Int: mostly small, sometimes negative, sometimes beyond every machine
    /// width.
    pub(super) fn index(&mut self, size: usize) -> BigInt {
        match self.below(16) {
            0 => -BigInt::from(1 + self.below(4)),
            1 => BigInt::from(1_u8) << 64_u32,
            2 => -(BigInt::from(1_u8) << 64_u32),
            3 => BigInt::from(size + self.below(3)),
            _ => BigInt::from(self.below(size + 2)),
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The check.

#[derive(Default, Debug)]
pub(super) struct Tally {
    /// Concrete instances compared with the model.
    pub(super) concrete: usize,
    /// Symbolic applications the hook decided (a value or `\bottom`).
    pub(super) symbolic_decided: usize,
    /// Symbolic applications the hook declined.
    pub(super) symbolic_declined: usize,
    /// Instances skipped because an argument is undefined under the assignment.
    pub(super) skipped: usize,
}

pub(super) type Tallies = BTreeMap<&'static str, Tally>;

/// `hook` applied to `arguments` by a symbol that declares its result as `domains.md` does.
pub(super) fn evaluate(hook: &str, arguments: &[Term]) -> Result<BuiltinResult, String> {
    match evaluate_hook_into(hook, arguments, result_collection(hook).as_ref()) {
        Ok(Ok(result)) => Ok(result),
        Ok(Err(error)) => Err(format!("{hook} failed: {error:?}")),
        Err(stop) => Err(format!("{hook} stopped: {stop:?}")),
    }
}

/// Whether a result value `actual` (`None`: undefined) is one `expect` admits.
fn admits(expect: &Expect, actual: Option<&Val>) -> bool {
    match (expect, actual) {
        (Expect::Open, _) => true,
        (Expect::Unspecified, _) => false,
        (Expect::Bottom, actual) => actual.is_none(),
        (_, None) => false,
        (Expect::Value(expected), Some(actual)) => expected == actual,
        (Expect::OneOf(choices), Some(actual)) => choices.contains(actual),
        (Expect::Permutation(expected), Some(Val::List(actual))) => {
            let (mut expected, mut actual) = (expected.clone(), actual.clone());
            expected.sort();
            actual.sort();
            expected == actual
        }
        (Expect::Permutation(_), Some(_)) => false,
    }
}

/// The value of a hook result under `env`: `Some(None)` for `\bottom` or an undefined value,
/// `None` when the hook declined.
fn outcome(result: &BuiltinResult, env: &Env) -> Result<Option<Option<Val>>, String> {
    match result {
        BuiltinResult::Value(term) => Ok(Some(decode(term, env))),
        BuiltinResult::Bottom => Ok(Some(None)),
        BuiltinResult::NotApplicable | BuiltinResult::Unsupported(_) => Ok(None),
        BuiltinResult::Effect(effect) => Err(format!("unexpected effect {effect:?}")),
    }
}

fn has_variables(arguments: &[Term]) -> bool {
    arguments
        .iter()
        .any(|argument| !argument.attributes().variables.is_empty())
}

/// Check one case against `model`, which maps the argument values to the documented result.
pub(super) fn check(
    case: &Case,
    model: &dyn Fn(&str, &[Val]) -> Spec,
    tallies: &RefCell<Tallies>,
) -> Result<(), TestCaseError> {
    let mut tallies = tallies.borrow_mut();
    let tally = tallies.entry(case.hook).or_default();
    let Some(inputs) = case
        .arguments
        .iter()
        .map(|argument| decode(argument, &case.env))
        .collect::<Option<Vec<_>>>()
    else {
        tally.skipped += 1;
        return Ok(());
    };
    let spec = model(case.hook, &inputs);
    let concrete_arguments = case
        .arguments
        .iter()
        .map(|argument| instantiate(argument, &case.env))
        .collect::<Vec<_>>();
    let fail = |message: String| {
        let mut report = String::new();
        let _ = writeln!(report, "{message}");
        let _ = writeln!(report, "hook: {}", case.hook);
        let _ = writeln!(report, "arguments: {:?}", case.arguments);
        let _ = writeln!(report, "assignment: {:?}", case.env);
        let _ = writeln!(report, "argument values: {inputs:?}");
        let _ = write!(report, "model: {spec:?}");
        TestCaseError::fail(report)
    };
    let concrete = evaluate(case.hook, &concrete_arguments).map_err(&fail)?;
    if matches!(spec.expect, Expect::Unspecified)
        && !matches!(
            concrete,
            BuiltinResult::Unsupported(UnsupportedHookReason::Unspecified { .. })
        )
    {
        return Err(fail(format!(
            "the hook gives {concrete:?} where its value is unspecified"
        )));
    }
    let concrete_value = outcome(&concrete, &Env::new()).map_err(&fail)?;
    match &concrete_value {
        None if !spec.may_decline => {
            return Err(fail(format!(
                "the hook declined concrete arguments: {concrete:?}"
            )));
        }
        None => {}
        Some(actual) if !admits(&spec.expect, actual.as_ref()) => {
            return Err(fail(format!(
                "concrete result {concrete:?} (value {actual:?}) disagrees with the model"
            )));
        }
        Some(_) => tally.concrete += 1,
    }
    if !has_variables(&case.arguments) {
        return Ok(());
    }
    let symbolic = evaluate(case.hook, &case.arguments).map_err(&fail)?;
    let Some(symbolic_value) = outcome(&symbolic, &case.env).map_err(&fail)? else {
        tally.symbolic_declined += 1;
        return Ok(());
    };
    tally.symbolic_decided += 1;
    if !admits(&spec.expect, symbolic_value.as_ref()) {
        return Err(fail(format!(
            "symbolic result {symbolic:?} denotes {symbolic_value:?} on this instance, which \
             the model does not admit"
        )));
    }
    if let Some(concrete_value) = concrete_value
        && concrete_value != symbolic_value
    {
        return Err(fail(format!(
            "symbolic result {symbolic:?} denotes {symbolic_value:?} on this instance, but \
             the concrete arguments give {concrete_value:?}"
        )));
    }
    Ok(())
}

/// Run `cases` generated cases of one hook family and return the per-hook tallies.
pub(super) fn run(
    cases: u32,
    generate: &dyn Fn(&mut Draw<'_>) -> Case,
    model: &dyn Fn(&str, &[Val]) -> Spec,
) -> Tallies {
    let tallies = RefCell::new(Tallies::new());
    let mut runner = TestRunner::new_with_rng(
        Config {
            cases,
            failure_persistence: None,
            ..Config::default()
        },
        TestRng::deterministic_rng(RngAlgorithm::ChaCha),
    );
    let result = runner.run(&vec(any::<u8>(), 0..192), |bytes: Vec<u8>| {
        let case = generate(&mut Draw::new(&bytes));
        check(&case, model, &tallies)
    });
    if let Err(error) = result {
        panic!("{error}");
    }
    tallies.into_inner()
}

/// Every hook in `hooks` was compared on concrete instances; the ones in `symbolic` also
/// decided some symbolic application. Prints the tallies.
pub(super) fn assert_reached(tallies: &Tallies, hooks: &[&str], symbolic: &[&str]) {
    for (hook, tally) in tallies {
        eprintln!("{hook}: {tally:?}");
    }
    for hook in hooks {
        let tally = tallies
            .get(hook)
            .unwrap_or_else(|| panic!("{hook} was never generated"));
        assert!(tally.concrete > 0, "{hook} was never compared: {tally:?}");
    }
    for hook in symbolic {
        assert!(
            tallies[hook].symbolic_decided > 0,
            "{hook} never decided a symbolic application: {:?}",
            tallies[hook]
        );
    }
}
