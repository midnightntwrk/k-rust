//! A randomized differential test of the definedness claims against a ground-truth oracle.
//!
//! Two claims of the backend say that a term is defined although no equation evaluates it to a
//! value: `\ceil(t)` simplifying to `\top` (the value certificate and instance normality, read
//! for a `value-production` head), and instance normality itself, which says that
//! every instance of `t` is a normal form the equations identify with no other one. This module
//! checks both against what the axioms of small definitions prove, without any of the backend's
//! code.
//!
//! The oracle reads a definition as its axioms: each equation `h(p1, …, pn) = r requires c`,
//! written as KORE binds each argument `Xi` of `h` by `Xi ∈ pi`, and so states `lσ = rσ` for
//! every valuation `σ` of its variables to values at which `c` holds and every `piσ` is
//! defined (an undefined `piσ` makes the membership false and the instance vacuous). It explores
//! ground terms (hash-consed, injections composed) by rewriting any subterm that syntactically
//! matches a left-hand side, evaluating `requires` only on Int literals (any other binding of
//! a `requires` variable skips the step) and `X /Int 0` to `\bottom`. From the steps it derives
//! the least sets `U` (provably undefined) and `D` (provably defined) closed under:
//!
//! - `\bottom` is in `U`; a term with a subterm in `U` is in `U` (application is strict);
//! - Int literals, and injections and applications of total symbols (constructors, and heads
//!   and functions declared `total`) whose arguments are in `D`, are in `D` (a total symbol is
//!   defined on defined arguments);
//! - an application of a total symbol that is in `U`, with every argument but one in `D`, puts
//!   that argument in `U` (were it defined too, the application would be);
//! - for a step `C[lσ] -> C[rσ]`: `C[rσ] ∈ U` implies `C[lσ] ∈ U`, always (if every value of `σ`
//!   and every `piσ` is defined the equation instance makes the two equal, and otherwise `lσ`
//!   has an undefined subterm); `C[lσ] ∈ D` implies `C[rσ] ∈ D` when every value of `σ` is in
//!   `D` (a defined `lσ` has defined arguments); and when every value of `σ` and every `piσ` is
//!   in `D`, the equation instance holds, so `C[lσ] ∈ U` implies `C[rσ] ∈ U` and `C[rσ] ∈ D`
//!   implies `C[lσ] ∈ D`.
//!
//! Each rule holds in every model of the axioms, so `t ∈ U` proves `t` undefined. A definition
//! whose exploration shows it inconsistent (`U` meets `D`, or two distinct constructor terms are
//! equal through steps whose instances hold) is skipped: there every claim is valid.
//!
//! The backend states an assumption it does not check (`instance_normal/patterns.rs`): a peak
//! that does not meet, at an instance of an equation of another head than an application's,
//! does not reach that application's head, no peak that does not meet binds, in its two
//! steps or in the steps its sides take, a value in which the application occurs, and no
//! equation of another, total head whose left-hand side holds the application below total
//! symbols has an undefined right-hand side there. The oracle applies it rather than testing
//! it: a query is not checked when some application the query reaches by steps has a head
//! that an overlap peak of the explored graph, whose two sides it cannot join, may make
//! undefined that way ([`Peak`]), or that a root step of a total head's equation to a term in
//! `U` holds below total symbols, or when a term the query reaches has a step whose redex has
//! an argument in `U` (the evaluator applies such an equation instance although it states
//! nothing, `docs/compatibility.md`, "Anywhere rules"). The assumption is the
//! certificate's, and the certificate never reads an application that one of its own head's
//! conditional equations matches as a value (the equation is never set aside, and a refuted
//! `requires` is not read as leaving the application free), so such an application, at an
//! exposed position of a normal form the query reaches, excuses nothing: its obligation must
//! stay.
//! A peak not shown joinable within the bound counts as not joinable, and a search cut short
//! counts every head, which only checks fewer queries.
//!
//! For every checked `t ∈ U`, and for the generalizations of `t` that replace a constructor
//! subterm by a variable (one of whose instances is `t`), `\ceil` must not simplify to `\top`
//! and instance normality must give no token; a panic (the test build's `check-normal-forms`
//! guard) is a failure too. Every definition is run under the default bounds of the pattern
//! facts and under minimal ones ([`Bounds`]), which lose precision only, so the claims must be
//! sound under both.
//!
//! `\ceil` is simplified only for a term every sequence of whose steps ends
//! ([`Universe::terminates`]): simplification evaluates the term, and the evaluation of a
//! definition that does not terminate need not end.
//!
//! The definitions are a fixed corpus encoding every reviewer probe of the value-production
//! definedness claims (the withdrawn `requires` discharge's and the pattern facts', each asserted
//! to have its query in `U`), variants of each
//! that write the same axioms with other variable names and equation orders ([`variant`]), and
//! seeded random ones. `KRUST_DEFINEDNESS_ORACLE_CASES` (default [`DEFAULT_CASES`]),
//! `KRUST_DEFINEDNESS_ORACLE_FIRST` and `KRUST_DEFINEDNESS_ORACLE_SEED` set the random run,
//! `KRUST_DEFINEDNESS_ORACLE_VARIANTS` the variants per probe; run with `--nocapture` for the
//! summaries, `KRUST_DEFINEDNESS_ORACLE_VERBOSE` for each definition and query.

use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque},
    fmt::Write as _,
    panic::{AssertUnwindSafe, catch_unwind},
    rc::Rc,
};

use k_rust_kore::kore::parser::{parse_definition, parse_pattern};

use crate::{
    definition::BackendDefinition,
    instance_normal::{Bounds, with_bounds},
    rule::Predicate,
    simplify::{SimplificationOptions, simplify_predicate_with_solver},
    smt::NoSolver,
};

/// Random definitions in the default run.
const DEFAULT_CASES: u64 = 24;

/// The seed of the default run.
const DEFAULT_SEED: u64 = 0x5eed_0006;

/// The bounds under which every definition is asked a second time: past each bound the
/// answers are the conservative ones, which small definitions reach only under these.
const MINIMAL: Bounds = Bounds {
    value_questions: 2,
    representatives: 2,
    representative_size: 8,
    narrowing_depth: 1,
    join_steps: 1,
    pattern_fact_rounds: 2,
    scan_work: 40,
    pattern_facts_work: 400,
};

// ---------------------------------------------------------------------------------------------
// The definition language.

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Pat {
    /// A variable: name, sort.
    Var(String, String),
    App(String, Vec<Pat>),
    Int(i64),
    /// `inj{from, to}(pattern)`.
    Inj(String, String, Box<Pat>),
    /// `divInt` (right-hand sides only).
    Div(Box<Pat>, Box<Pat>),
}

fn var(name: &str, sort: &str) -> Pat {
    Pat::Var(name.into(), sort.into())
}

fn app(name: &str, arguments: Vec<Pat>) -> Pat {
    Pat::App(name.into(), arguments)
}

fn cons(name: &str) -> Pat {
    app(name, Vec::new())
}

fn int(value: i64) -> Pat {
    Pat::Int(value)
}

fn inj(from: &str, to: &str, pattern: Pat) -> Pat {
    Pat::Inj(from.into(), to.into(), Box::new(pattern))
}

fn div(left: Pat, right: Pat) -> Pat {
    Pat::Div(Box::new(left), Box::new(right))
}

/// `mk(1 /Int 0)`: undefined.
fn undefined() -> Pat {
    app("mk", vec![div(int(1), int(0))])
}

#[derive(Clone, Copy, Debug)]
enum Comparison {
    Eq,
    Lt,
}

/// `variable <op> value` over Int.
#[derive(Clone, Debug)]
struct Requires {
    comparison: Comparison,
    variable: String,
    value: i64,
}

fn requires_eq(variable: &str, value: i64) -> Option<Requires> {
    Some(Requires {
        comparison: Comparison::Eq,
        variable: variable.into(),
        value,
    })
}

#[derive(Clone, Debug)]
struct Equation {
    lhs: Pat,
    rhs: Pat,
    requires: Option<Requires>,
}

#[derive(Clone, Debug)]
struct Symbol {
    name: String,
    arguments: Vec<String>,
    result: String,
    constructor: bool,
    /// For a symbol that is not a constructor: whether it is declared total, and how.
    totality: Totality,
}

/// How a symbol that is not a constructor is declared.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Totality {
    /// `anywhere, function, value-production`: partial, its equations decide it.
    Production,
    /// `anywhere, total`: an equation head defined on defined arguments.
    Head,
    /// `function, total`: a declared function defined on defined arguments, with no equations
    /// here.
    Function,
}

/// A definition over the hooked `Int` and `Bool`, with the sorts, subsorts, constructors,
/// value-production heads, total heads and functions, and anywhere equations given;
/// `mk : Int -> S` is always declared.
#[derive(Clone, Debug, Default)]
struct Definition {
    sorts: Vec<String>,
    subsorts: Vec<(String, String)>,
    symbols: Vec<Symbol>,
    equations: Vec<Equation>,
}

impl Definition {
    fn new(sorts: &[&str]) -> Self {
        let mut definition = Self::default();
        definition.sorts.push("S".into());
        for sort in sorts {
            if *sort != "S" {
                definition.sorts.push((*sort).into());
            }
        }
        definition.constructor("mk", &["Int"], "S")
    }

    fn symbol(
        mut self,
        name: &str,
        arguments: &[&str],
        result: &str,
        constructor: bool,
        totality: Totality,
    ) -> Self {
        self.symbols.push(Symbol {
            name: name.into(),
            arguments: arguments.iter().map(|sort| (*sort).into()).collect(),
            result: result.into(),
            constructor,
            totality,
        });
        self
    }

    fn constructor(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, true, Totality::Production)
    }

    fn head(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, false, Totality::Production)
    }

    /// An `anywhere` equation head declared `total`.
    fn total_head(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, false, Totality::Head)
    }

    /// A function declared `total`, with no equations.
    fn total_function(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, false, Totality::Function)
    }

    /// `sub < sup`; the closure must be given explicitly.
    fn subsort(mut self, sub: &str, sup: &str) -> Self {
        self.subsorts.push((sub.into(), sup.into()));
        self
    }

    fn equation(self, lhs: Pat, rhs: Pat) -> Self {
        self.conditional(lhs, rhs, None)
    }

    fn conditional(mut self, lhs: Pat, rhs: Pat, requires: Option<Requires>) -> Self {
        self.equations.push(Equation { lhs, rhs, requires });
        self
    }

    fn symbol_named(&self, name: &str) -> &Symbol {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .unwrap_or_else(|| panic!("undeclared symbol {name}"))
    }

    fn kore(&self) -> String {
        let mut source = String::from(
            r#"[]
module MAIN
hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
hooked-symbol divInt{}(SortInt{}, SortInt{}) : SortInt{} [function{}(), hook{}("INT.tdiv"), smt-hook{}("div")]
hooked-symbol eqInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
hooked-symbol ltInt{}(SortInt{}, SortInt{}) : SortBool{} [function{}(), total{}(), hook{}("INT.lt"), smt-hook{}("<")]
"#,
        );
        for sort in &self.sorts {
            writeln!(source, "sort Sort{sort}{{}} []").unwrap();
        }
        if !self.subsorts.is_empty() {
            source.push_str("symbol inj{From, To}(From) : To [sortInjection{}()]\n");
        }
        for (sub, sup) in &self.subsorts {
            let (sub, sup) = (sort_kore(sub), sort_kore(sup));
            writeln!(
                source,
                r"axiom{{R}} \exists{{R}}(Value:{sup}, \equals{{{sup}, R}}(Value:{sup}, inj{{{sub}, {sup}}}(From:{sub}))) [subsort{{{sub}, {sup}}}()]"
            )
            .unwrap();
        }
        for symbol in &self.symbols {
            let attributes = match (symbol.constructor, symbol.totality) {
                (true, _) => "constructor{}(), functional{}(), injective{}()",
                (false, Totality::Production) => "anywhere{}(), function{}(), value-production{}()",
                (false, Totality::Head) => "anywhere{}(), total{}()",
                (false, Totality::Function) => "function{}(), total{}()",
            };
            writeln!(
                source,
                "symbol {}{{}}({}) : {} [{attributes}]",
                symbol.name,
                symbol
                    .arguments
                    .iter()
                    .map(|sort| sort_kore(sort))
                    .collect::<Vec<_>>()
                    .join(", "),
                sort_kore(&symbol.result)
            )
            .unwrap();
        }
        for equation in &self.equations {
            source.push_str(&self.equation_kore(equation));
            source.push('\n');
        }
        source.push_str("endmodule []\n");
        source
    }

    fn equation_kore(&self, equation: &Equation) -> String {
        let Pat::App(head, arguments) = &equation.lhs else {
            panic!("a left-hand side is a head application")
        };
        let symbol = self.symbol_named(head);
        let memberships = arguments
            .iter()
            .zip(&symbol.arguments)
            .enumerate()
            .rev()
            .fold(
                r"\top{R}()".to_string(),
                |rest, (index, (argument, sort))| {
                    let sort = sort_kore(sort);
                    format!(
                        r"\and{{R}}(\in{{{sort}, R}}(X{index}:{sort}, {}), {rest})",
                        pattern_kore(argument)
                    )
                },
            );
        let requires = match &equation.requires {
            None => r"\top{R}()".to_string(),
            Some(requires) => format!(
                r#"\equals{{SortBool{{}}, R}}({}{{}}({}:SortInt{{}}, \dv{{SortInt{{}}}}("{}")), \dv{{SortBool{{}}}}("true"))"#,
                match requires.comparison {
                    Comparison::Eq => "eqInt",
                    Comparison::Lt => "ltInt",
                },
                requires.variable,
                requires.value
            ),
        };
        let result = sort_kore(&symbol.result);
        let parameters = symbol
            .arguments
            .iter()
            .enumerate()
            .map(|(index, sort)| format!("X{index}:{}", sort_kore(sort)))
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({}, \top{{{result}}}()))) [anywhere{{}}()]",
            pattern_kore(&equation.rhs)
        )
    }
}

fn sort_kore(sort: &str) -> String {
    format!("Sort{sort}{{}}")
}

fn pattern_kore(pattern: &Pat) -> String {
    match pattern {
        Pat::Var(name, sort) => format!("{name}:{}", sort_kore(sort)),
        Pat::App(name, arguments) => format!(
            "{name}{{}}({})",
            arguments
                .iter()
                .map(pattern_kore)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Pat::Int(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
        Pat::Inj(from, to, pattern) => format!(
            "inj{{{}, {}}}({})",
            sort_kore(from),
            sort_kore(to),
            pattern_kore(pattern)
        ),
        Pat::Div(left, right) => {
            format!(
                "divInt{{}}({}, {})",
                pattern_kore(left),
                pattern_kore(right)
            )
        }
    }
}

fn pattern_variables(pattern: &Pat, into: &mut BTreeMap<String, String>) {
    match pattern {
        Pat::Var(name, sort) => {
            into.insert(name.clone(), sort.clone());
        }
        Pat::App(_, arguments) => {
            for argument in arguments {
                pattern_variables(argument, into);
            }
        }
        Pat::Int(_) => {}
        Pat::Inj(_, _, pattern) => pattern_variables(pattern, into),
        Pat::Div(left, right) => {
            pattern_variables(left, into);
            pattern_variables(right, into);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The oracle.

type Id = u32;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Node {
    Bottom,
    Int(i64),
    App(u32, Vec<Id>),
    Inj(u32, u32, Id),
}

const BOTTOM: Id = 0;

/// One step from a term: the reduct, the values of the valuation, the position of the redex
/// and the head of the equation that rewrote it.
#[derive(Clone, Debug)]
struct Step {
    to: Id,
    valuation: Vec<Id>,
    /// The arguments of the redex: the instances of the left-hand side's argument patterns,
    /// each of which the equation binds to its argument variable by membership, so the
    /// equation instance holds only where they are defined.
    arguments: Vec<Id>,
    path: Vec<u8>,
    head: u32,
}

struct Universe<'d> {
    definition: &'d Definition,
    symbols: HashMap<&'d str, u32>,
    sorts: HashMap<&'d str, u32>,
    /// `below[a][b]`: `a` is a strict subsort of `b`.
    below: Vec<Vec<bool>>,
    nodes: Vec<Node>,
    ids: HashMap<Node, Id>,
    sizes: Vec<u32>,
    steps: HashMap<Id, Rc<Vec<Step>>>,
    /// The terms whose evaluation by the backend is not known to end: those an equation
    /// rewrites to themselves or to a term the oracle does not build (a division of an
    /// unevaluated operand), neither recorded as a step, and those an equation rewrites to a
    /// right-hand side with a division under an equation head (`g(J, Z) = g(J /Int 0, Z)`) or
    /// over one (`h(c) = mk(f(0) /Int 0)`): the oracle reads a division by zero as `\bottom`
    /// at once, while the backend may keep it as an argument and apply the equation to the
    /// result again, or evaluate the operand first, which need not end.
    loops: HashSet<Id>,
}

/// Exploration bounds.
const MAX_NODES: usize = 3000;
const MAX_SIZE: u32 = 14;
const QUERY_SIZE: u32 = 12;
const QUERIES: usize = 24;
const JOIN_SEARCH: usize = 300;

impl<'d> Universe<'d> {
    fn new(definition: &'d Definition) -> Self {
        let mut sorts = HashMap::new();
        sorts.insert("Int", 0);
        for sort in &definition.sorts {
            let next = u32::try_from(sorts.len()).unwrap();
            sorts.entry(sort.as_str()).or_insert(next);
        }
        let mut below = vec![vec![false; sorts.len()]; sorts.len()];
        for (sub, sup) in &definition.subsorts {
            below[sorts[sub.as_str()] as usize][sorts[sup.as_str()] as usize] = true;
        }
        let symbols = definition
            .symbols
            .iter()
            .enumerate()
            .map(|(index, symbol)| (symbol.name.as_str(), u32::try_from(index).unwrap()))
            .collect();
        let mut universe = Self {
            definition,
            symbols,
            sorts,
            below,
            nodes: Vec::new(),
            ids: HashMap::new(),
            sizes: Vec::new(),
            steps: HashMap::new(),
            loops: HashSet::new(),
        };
        universe.intern(Node::Bottom);
        universe
    }

    fn intern(&mut self, node: Node) -> Id {
        if let Some(id) = self.ids.get(&node) {
            return *id;
        }
        let size = match &node {
            Node::Bottom | Node::Int(_) => 1,
            Node::App(_, arguments) => {
                1 + arguments
                    .iter()
                    .map(|argument| self.sizes[*argument as usize])
                    .sum::<u32>()
            }
            Node::Inj(_, _, argument) => 1 + self.sizes[*argument as usize],
        };
        let id = Id::try_from(self.nodes.len()).unwrap();
        self.nodes.push(node.clone());
        self.sizes.push(size);
        self.ids.insert(node, id);
        id
    }

    /// A node, `\bottom` when an argument is, injections composed.
    fn node(&mut self, node: Node) -> Id {
        match &node {
            Node::App(_, arguments) if arguments.contains(&BOTTOM) => BOTTOM,
            Node::Inj(_, _, argument) if *argument == BOTTOM => BOTTOM,
            Node::Inj(from, to, argument) if from == to => *argument,
            Node::Inj(_, to, argument) => match self.nodes[*argument as usize].clone() {
                Node::Inj(inner, _, operand) => self.node(Node::Inj(inner, *to, operand)),
                _ => self.intern(node),
            },
            _ => self.intern(node),
        }
    }

    fn sort(&self, sort: &str) -> u32 {
        self.sorts[sort]
    }

    fn ground(&mut self, pattern: &Pat) -> Id {
        self.instantiate(pattern, &HashMap::new())
            .expect("a ground pattern evaluates")
    }

    fn matches(&mut self, pattern: &Pat, id: Id, valuation: &mut HashMap<String, Id>) -> bool {
        match pattern {
            Pat::Var(name, _) => match valuation.get(name) {
                Some(bound) => *bound == id,
                None => {
                    valuation.insert(name.clone(), id);
                    true
                }
            },
            Pat::Int(value) => self.nodes[id as usize] == Node::Int(*value),
            Pat::App(name, arguments) => {
                let Node::App(symbol, children) = self.nodes[id as usize].clone() else {
                    return false;
                };
                symbol == self.symbols[name.as_str()]
                    && arguments.len() == children.len()
                    && arguments
                        .iter()
                        .zip(children)
                        .all(|(argument, child)| self.matches(argument, child, valuation))
            }
            Pat::Inj(from, to, inner) => {
                let Node::Inj(source, target, operand) = self.nodes[id as usize].clone() else {
                    return false;
                };
                let (from, to) = (self.sort(from), self.sort(to));
                if target != to {
                    false
                } else if source == from {
                    self.matches(inner, operand, valuation)
                } else if self.below[source as usize][from as usize] {
                    let lifted = self.node(Node::Inj(source, from, operand));
                    self.matches(inner, lifted, valuation)
                } else {
                    false
                }
            }
            Pat::Div(..) => false,
        }
    }

    /// The instance of `pattern`; `None` when a division has an operand that is not a literal
    /// and a divisor other than zero.
    fn instantiate(&mut self, pattern: &Pat, valuation: &HashMap<String, Id>) -> Option<Id> {
        Some(match pattern {
            Pat::Var(name, _) => valuation[name],
            Pat::Int(value) => self.node(Node::Int(*value)),
            Pat::App(name, arguments) => {
                let children = arguments
                    .iter()
                    .map(|argument| self.instantiate(argument, valuation))
                    .collect::<Option<Vec<_>>>()?;
                let symbol = self.symbols[name.as_str()];
                self.node(Node::App(symbol, children))
            }
            Pat::Inj(from, to, inner) => {
                let operand = self.instantiate(inner, valuation)?;
                let (from, to) = (self.sort(from), self.sort(to));
                self.node(Node::Inj(from, to, operand))
            }
            Pat::Div(left, right) => {
                let left = self.instantiate(left, valuation)?;
                let right = self.instantiate(right, valuation)?;
                if left == BOTTOM || right == BOTTOM {
                    return Some(BOTTOM);
                }
                match (&self.nodes[left as usize], &self.nodes[right as usize]) {
                    (_, Node::Int(0)) => BOTTOM,
                    (Node::Int(dividend), Node::Int(divisor)) => {
                        let quotient = dividend / divisor;
                        self.node(Node::Int(quotient))
                    }
                    _ => return None,
                }
            }
        })
    }

    /// Whether `pattern` has a division below an application of an equation head
    /// (`under_head` when `pattern` itself is below one).
    fn divides_under_head(&self, pattern: &Pat, under_head: bool) -> bool {
        match pattern {
            Pat::Div(left, right) => {
                under_head
                    || self.divides_under_head(left, under_head)
                    || self.divides_under_head(right, under_head)
            }
            Pat::App(name, arguments) => {
                let head = !self.definition.symbol_named(name).constructor;
                arguments
                    .iter()
                    .any(|argument| self.divides_under_head(argument, under_head || head))
            }
            Pat::Inj(_, _, inner) => self.divides_under_head(inner, under_head),
            Pat::Var(..) | Pat::Int(_) => false,
        }
    }

    /// Whether `pattern` has a division with an equation head application in an operand.
    fn divides_a_head(&self, pattern: &Pat) -> bool {
        match pattern {
            Pat::Div(left, right) => self.has_head(left) || self.has_head(right),
            Pat::App(_, arguments) => arguments
                .iter()
                .any(|argument| self.divides_a_head(argument)),
            Pat::Inj(_, _, inner) => self.divides_a_head(inner),
            Pat::Var(..) | Pat::Int(_) => false,
        }
    }

    /// Whether `pattern` has an application of an equation head.
    fn has_head(&self, pattern: &Pat) -> bool {
        match pattern {
            Pat::App(name, arguments) => {
                !self.definition.symbol_named(name).constructor
                    || arguments.iter().any(|argument| self.has_head(argument))
            }
            Pat::Div(left, right) => self.has_head(left) || self.has_head(right),
            Pat::Inj(_, _, inner) => self.has_head(inner),
            Pat::Var(..) | Pat::Int(_) => false,
        }
    }

    fn holds(&self, requires: Option<&Requires>, valuation: &HashMap<String, Id>) -> bool {
        let Some(requires) = requires else {
            return true;
        };
        let Some(Node::Int(value)) = valuation
            .get(&requires.variable)
            .map(|id| &self.nodes[*id as usize])
        else {
            return false;
        };
        match requires.comparison {
            Comparison::Eq => *value == requires.value,
            Comparison::Lt => *value < requires.value,
        }
    }

    fn steps(&mut self, id: Id) -> Rc<Vec<Step>> {
        if let Some(steps) = self.steps.get(&id) {
            return Rc::clone(steps);
        }
        let mut steps = Vec::new();
        let node = self.nodes[id as usize].clone();
        if let Node::App(symbol, _) = node {
            let definition = self.definition;
            for equation in &definition.equations {
                let Pat::App(head, _) = &equation.lhs else {
                    continue;
                };
                if self.symbols[head.as_str()] != symbol {
                    continue;
                }
                let mut valuation = HashMap::new();
                if !self.matches(&equation.lhs, id, &mut valuation)
                    || !self.holds(equation.requires.as_ref(), &valuation)
                {
                    continue;
                }
                if self.divides_under_head(&equation.rhs, false)
                    || self.divides_a_head(&equation.rhs)
                {
                    self.loops.insert(id);
                }
                let Some(to) = self.instantiate(&equation.rhs, &valuation) else {
                    self.loops.insert(id);
                    continue;
                };
                if to == id {
                    self.loops.insert(id);
                } else {
                    steps.push(Step {
                        to,
                        valuation: valuation.values().copied().collect(),
                        arguments: self.children(id),
                        path: Vec::new(),
                        head: symbol,
                    });
                }
            }
        }
        let children = match &node {
            Node::App(_, children) => children.clone(),
            Node::Inj(_, _, child) => vec![*child],
            Node::Bottom | Node::Int(_) => Vec::new(),
        };
        for (index, child) in children.iter().enumerate() {
            for step in self.steps(*child).iter() {
                let to = match &node {
                    Node::App(symbol, children) => {
                        let mut children = children.clone();
                        children[index] = step.to;
                        self.node(Node::App(*symbol, children))
                    }
                    Node::Inj(from, target, _) => self.node(Node::Inj(*from, *target, step.to)),
                    Node::Bottom | Node::Int(_) => unreachable!("no children"),
                };
                let mut path = vec![u8::try_from(index).unwrap()];
                path.extend(&step.path);
                steps.push(Step {
                    to,
                    valuation: step.valuation.clone(),
                    arguments: step.arguments.clone(),
                    path,
                    head: step.head,
                });
            }
        }
        let steps = Rc::new(steps);
        self.steps.insert(id, Rc::clone(&steps));
        steps
    }

    fn children(&self, id: Id) -> Vec<Id> {
        match &self.nodes[id as usize] {
            Node::App(_, children) => children.clone(),
            Node::Inj(_, _, child) => vec![*child],
            Node::Bottom | Node::Int(_) => Vec::new(),
        }
    }

    fn is_constructor(&self, symbol: u32) -> bool {
        self.definition.symbols[symbol as usize].constructor
    }

    /// Whether an application of `symbol` is defined whenever its arguments are: a constructor,
    /// or a symbol declared `total`.
    fn is_total(&self, symbol: u32) -> bool {
        let symbol = &self.definition.symbols[symbol as usize];
        symbol.constructor || symbol.totality != Totality::Production
    }

    /// The value-production heads of the applications in the term, but those in `skip` at an
    /// exposed position (the term itself, or below total symbols and injections only).
    fn heads(&self, id: Id, skip: &HashSet<Id>, into: &mut BTreeSet<u32>) {
        self.heads_below(id, true, skip, into);
    }

    fn heads_below(&self, id: Id, exposed: bool, skip: &HashSet<Id>, into: &mut BTreeSet<u32>) {
        let mut exposed = exposed;
        if let Node::App(symbol, _) = &self.nodes[id as usize] {
            if !self.is_constructor(*symbol) && !(exposed && skip.contains(&id)) {
                into.insert(*symbol);
            }
            exposed &= self.is_total(*symbol);
        }
        for child in self.children(id) {
            self.heads_below(child, exposed, skip, into);
        }
    }

    /// The heads of the applications a term's definedness rests on directly: its own, and,
    /// under total symbols and injections, its arguments'. A term identified with `\bottom`
    /// makes one of these undefined; one under a partial head need not be.
    fn exposed_heads(&self, id: Id, into: &mut BTreeSet<u32>) {
        if let Node::App(symbol, _) = &self.nodes[id as usize] {
            if !self.is_constructor(*symbol) {
                into.insert(*symbol);
            }
            if !self.is_total(*symbol) {
                return;
            }
        }
        for child in self.children(id) {
            self.exposed_heads(child, into);
        }
    }

    /// Explores from `seeds`, breadth first, up to [`MAX_NODES`] nodes, expanding terms up to
    /// [`MAX_SIZE`]; returns the expanded terms.
    fn explore(&mut self, seeds: &[Id]) -> Vec<Id> {
        let mut queue = seeds.iter().copied().collect::<VecDeque<_>>();
        let mut seen = seeds.iter().copied().collect::<HashSet<_>>();
        let mut expanded = Vec::new();
        while let Some(id) = queue.pop_front() {
            if self.nodes.len() > MAX_NODES {
                break;
            }
            if id == BOTTOM || self.sizes[id as usize] > MAX_SIZE {
                continue;
            }
            expanded.push(id);
            let steps = self.steps(id);
            for next in steps
                .iter()
                .map(|step| step.to)
                .chain(self.children(id))
                .collect::<Vec<_>>()
            {
                if seen.insert(next) {
                    queue.push_back(next);
                }
            }
        }
        expanded
    }

    /// The terms the explored steps reach from `from`, and whether the search was complete:
    /// every term reached had its steps computed.
    fn reachable(&self, from: Id) -> (HashSet<Id>, bool) {
        let mut seen = HashSet::from([from]);
        let mut queue = VecDeque::from([from]);
        while let Some(id) = queue.pop_front() {
            if seen.len() > JOIN_SEARCH {
                return (seen, false);
            }
            if id != BOTTOM && !self.steps.contains_key(&id) {
                // Not expanded: the exploration stopped before it, or it is too large.
                return (seen, false);
            }
            if let Some(steps) = self.steps.get(&id) {
                for step in steps.iter() {
                    if seen.insert(step.to) {
                        queue.push_back(step.to);
                    }
                }
            }
        }
        (seen, true)
    }

    /// Whether every sequence of steps from `from` ends: the search is complete and the terms
    /// it reaches have no cycle, nor a subterm an equation rewrites to itself. Evaluation of a term with such a sequence need not end (`g(c)`
    /// under `g(Z) = g(q(Z, Z))` grows without bound), and the backend evaluates the terms it
    /// is asked to `\ceil`.
    fn terminates(&self, from: Id) -> bool {
        let (reached, complete) = self.reachable(from);
        if !complete || reached.iter().any(|id| self.has_loop(*id)) {
            return false;
        }
        // Kahn's algorithm on the reached subgraph: acyclic iff every term is removed.
        let mut incoming = reached
            .iter()
            .map(|id| (*id, 0usize))
            .collect::<HashMap<_, _>>();
        for id in &reached {
            for step in self.steps.get(id).map_or(&[][..], |steps| steps.as_slice()) {
                *incoming.get_mut(&step.to).expect("a reached term") += 1;
            }
        }
        let mut ready = incoming
            .iter()
            .filter(|(_, count)| **count == 0)
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        let mut removed = 0;
        while let Some(id) = ready.pop() {
            removed += 1;
            for step in self
                .steps
                .get(&id)
                .map_or(&[][..], |steps| steps.as_slice())
            {
                let count = incoming.get_mut(&step.to).expect("a reached term");
                *count -= 1;
                if *count == 0 {
                    ready.push(step.to);
                }
            }
        }
        removed == reached.len()
    }

    /// Whether `id` or one of its subterms is in [`Self::loops`].
    fn has_loop(&self, id: Id) -> bool {
        self.loops.contains(&id)
            || self
                .children(id)
                .into_iter()
                .any(|child| self.has_loop(child))
    }

    fn kore(&self, id: Id, generalized: Option<(Id, &str)>) -> String {
        if let Some((target, variable)) = generalized
            && target == id
        {
            return variable.to_string();
        }
        match &self.nodes[id as usize] {
            Node::Bottom => unreachable!("no query contains \\bottom"),
            Node::Int(value) => format!(r#"\dv{{SortInt{{}}}}("{value}")"#),
            Node::App(symbol, children) => format!(
                "{}{{}}({})",
                self.definition.symbols[*symbol as usize].name,
                children
                    .iter()
                    .map(|child| self.kore(*child, generalized))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            Node::Inj(from, to, child) => format!(
                "inj{{{}, {}}}({})",
                self.sort_kore_of(*from),
                self.sort_kore_of(*to),
                self.kore(*child, generalized)
            ),
        }
    }

    fn sort_kore_of(&self, sort: u32) -> String {
        let name = self
            .sorts
            .iter()
            .find(|(_, index)| **index == sort)
            .map(|(name, _)| *name)
            .unwrap();
        sort_kore(name)
    }

    fn sort_of(&self, id: Id) -> String {
        match &self.nodes[id as usize] {
            Node::Bottom => unreachable!("no query contains \\bottom"),
            Node::Int(_) => sort_kore("Int"),
            Node::App(symbol, _) => sort_kore(&self.definition.symbols[*symbol as usize].result),
            Node::Inj(_, to, _) => self.sort_kore_of(*to),
        }
    }
}

/// An overlap peak whose sides the exploration does not join.
struct Peak {
    /// The head of the equation at whose instance it is.
    head: u32,
    /// The heads of the applications the definedness of the terms its sides reach rests on
    /// directly ([`Universe::exposed_heads`]).
    exposed: BTreeSet<u32>,
    /// The heads of the applications in the values its two steps, and the steps its sides
    /// take, bind (and those steps' redexes' arguments, where its sides are proven one defined
    /// and one undefined), and in what those values reach: the equation instances of the two
    /// paths cannot all hold, so one of those values may be undefined.
    bound: BTreeSet<u32>,
}

/// What the oracle proves about one definition.
struct Verdicts {
    universe_size: usize,
    inconsistent: bool,
    /// Queries: a term in `U` (as KORE), its sort, and whether the assumption excuses it.
    queries: Vec<Query>,
    /// The terms in `U`, as KORE, for the corpus's coverage assertions.
    undefined: HashSet<String>,
}

struct Query {
    term: String,
    sort: String,
    excused: bool,
    /// Every sequence of steps from the term ends ([`Universe::terminates`]), so its
    /// evaluation, which `\ceil` simplification performs, ends.
    terminates: bool,
}

fn values_of_sort(universe: &mut Universe<'_>, sort: &str, literals: &[i64]) -> Vec<Id> {
    let definition = universe.definition;
    if sort == "Int" {
        return literals
            .iter()
            .map(|value| universe.node(Node::Int(*value)))
            .collect();
    }
    let mut values = Vec::new();
    for depth in 0..2 {
        for symbol in definition
            .symbols
            .iter()
            .filter(|symbol| symbol.result == sort && symbol.constructor)
        {
            if (depth == 0) != symbol.arguments.is_empty() {
                continue;
            }
            let arguments = symbol
                .arguments
                .iter()
                .map(|argument| {
                    if argument == sort {
                        values.first().copied()
                    } else {
                        values_of_sort_shallow(universe, argument, literals)
                    }
                })
                .collect::<Option<Vec<_>>>();
            if let Some(arguments) = arguments {
                let symbol = universe.symbols[symbol.name.as_str()];
                values.push(universe.node(Node::App(symbol, arguments)));
            }
        }
    }
    for (sub, sup) in &definition.subsorts {
        if sup == sort
            && let Some(operand) = values_of_sort_shallow(universe, sub, literals)
        {
            let (from, to) = (universe.sort(sub), universe.sort(sup));
            values.push(universe.node(Node::Inj(from, to, operand)));
        }
    }
    values.truncate(8);
    values
}

fn values_of_sort_shallow(universe: &mut Universe<'_>, sort: &str, literals: &[i64]) -> Option<Id> {
    if sort == "Int" {
        return literals
            .first()
            .map(|value| universe.node(Node::Int(*value)));
    }
    let definition = universe.definition;
    let symbol = definition.symbols.iter().find(|symbol| {
        symbol.result == sort && symbol.constructor && symbol.arguments.is_empty()
    })?;
    let symbol = universe.symbols[symbol.name.as_str()];
    Some(universe.node(Node::App(symbol, Vec::new())))
}

fn literals(definition: &Definition) -> Vec<i64> {
    fn collect(pattern: &Pat, into: &mut BTreeSet<i64>) {
        match pattern {
            Pat::Int(value) => {
                into.insert(*value);
            }
            Pat::App(_, arguments) => arguments
                .iter()
                .for_each(|argument| collect(argument, into)),
            Pat::Inj(_, _, pattern) => collect(pattern, into),
            Pat::Div(left, right) => {
                collect(left, into);
                collect(right, into);
            }
            Pat::Var(..) => {}
        }
    }
    let mut literals = BTreeSet::from([0, 1, 2, 3]);
    for equation in &definition.equations {
        collect(&equation.lhs, &mut literals);
        collect(&equation.rhs, &mut literals);
        if let Some(requires) = &equation.requires {
            literals.insert(requires.value);
        }
    }
    literals.into_iter().collect()
}

/// Seeds: up to 48 ground instances of each left-hand side over small values, and `extra`.
fn seeds(universe: &mut Universe<'_>, extra: &[Pat], rng: &mut Rng) -> Vec<Id> {
    let definition = universe.definition;
    let literals = literals(definition);
    let mut seeds = Vec::new();
    for equation in &definition.equations {
        let mut variables = BTreeMap::new();
        pattern_variables(&equation.lhs, &mut variables);
        let pools = variables
            .iter()
            .map(|(name, sort)| (name.clone(), values_of_sort(universe, sort, &literals)))
            .collect::<Vec<_>>();
        if pools.iter().any(|(_, pool)| pool.is_empty()) {
            continue;
        }
        let combinations = pools
            .iter()
            .map(|(_, pool)| pool.len())
            .try_fold(1usize, usize::checked_mul)
            .unwrap_or(usize::MAX);
        let count = combinations.min(48);
        for index in 0..count {
            let mut valuation = HashMap::new();
            let mut rest = index;
            for (name, pool) in &pools {
                let choice = if combinations <= 48 {
                    let choice = rest % pool.len();
                    rest /= pool.len();
                    choice
                } else {
                    rng.below(pool.len())
                };
                valuation.insert(name.clone(), pool[choice]);
            }
            if let Some(seed) = universe.instantiate(&equation.lhs, &valuation) {
                seeds.push(seed);
            }
        }
    }
    for pattern in extra {
        seeds.push(universe.ground(pattern));
    }
    seeds
}

fn oracle(definition: &Definition, extra: &[Pat], queries: &[Pat], rng: &mut Rng) -> Verdicts {
    let mut universe = Universe::new(definition);
    let mut seeds = seeds(&mut universe, extra, rng);
    for query in queries {
        seeds.push(universe.ground(query));
    }
    let expanded = universe.explore(&seeds);
    let count = universe.nodes.len();
    let mut undefined = vec![false; count];
    let mut defined = vec![false; count];
    undefined[BOTTOM as usize] = true;
    let edges = expanded
        .iter()
        .flat_map(|from| {
            universe.steps[from]
                .iter()
                .map(|step| {
                    // The equation instance holds where the valuation's values and the redex's
                    // arguments are defined.
                    let mut instance = step.valuation.clone();
                    instance.extend(&step.arguments);
                    (*from, step.to, step.valuation.clone(), instance)
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut changed = true;
    while changed {
        changed = false;
        for id in 1..count {
            let children = universe.children(Id::try_from(id).unwrap());
            if !undefined[id] && children.iter().any(|child| undefined[*child as usize]) {
                undefined[id] = true;
                changed = true;
            }
            if !defined[id] {
                let total = match &universe.nodes[id] {
                    Node::Int(_) | Node::Inj(..) => true,
                    Node::App(symbol, _) => universe.is_total(*symbol),
                    Node::Bottom => false,
                };
                if total && children.iter().all(|child| defined[*child as usize]) {
                    defined[id] = true;
                    changed = true;
                }
            }
            // A total application with every argument but one defined is undefined only when
            // that argument is.
            let total_application = match &universe.nodes[id] {
                Node::App(symbol, _) => universe.is_total(*symbol),
                Node::Inj(..) => true,
                Node::Bottom | Node::Int(_) => false,
            };
            if total_application && undefined[id] {
                let mut open = children.iter().filter(|child| !defined[**child as usize]);
                if let (Some(only), None) = (open.next(), open.next())
                    && !undefined[*only as usize]
                {
                    undefined[*only as usize] = true;
                    changed = true;
                }
            }
        }
        for (from, to, valuation, instance) in &edges {
            let (from, to) = (*from as usize, *to as usize);
            if undefined[to] && !undefined[from] {
                undefined[from] = true;
                changed = true;
            }
            if defined[from]
                && !defined[to]
                && valuation.iter().all(|value| defined[*value as usize])
            {
                defined[to] = true;
                changed = true;
            }
            if instance.iter().all(|value| defined[*value as usize]) {
                if undefined[from] && !undefined[to] {
                    undefined[to] = true;
                    changed = true;
                }
                if defined[to] && !defined[from] {
                    defined[from] = true;
                    changed = true;
                }
            }
        }
    }
    // Distinct constructor terms are distinct values: an equality between two shows the
    // explored axioms inconsistent.
    let mut pure = vec![false; count];
    for id in 1..count {
        pure[id] = match &universe.nodes[id] {
            Node::Int(_) | Node::Inj(..) => true,
            Node::App(symbol, _) => universe.is_constructor(*symbol),
            Node::Bottom => false,
        } && universe
            .children(Id::try_from(id).unwrap())
            .iter()
            .all(|child| pure[*child as usize]);
    }
    let mut parent = (0..count).collect::<Vec<_>>();
    fn find(parent: &mut [usize], mut node: usize) -> usize {
        while parent[node] != node {
            parent[node] = parent[parent[node]];
            node = parent[node];
        }
        node
    }
    for (from, to, _, instance) in &edges {
        if instance.iter().all(|value| defined[*value as usize]) {
            let (from, to) = (
                find(&mut parent, *from as usize),
                find(&mut parent, *to as usize),
            );
            parent[from] = to;
        }
    }
    let mut representative = HashMap::new();
    let mut confusion = false;
    for (id, _) in pure.iter().enumerate().skip(1).filter(|(_, pure)| **pure) {
        let class = find(&mut parent, id);
        if *representative.entry(class).or_insert(id) != id {
            confusion = true;
        }
    }
    let inconsistent = confusion || (1..count).any(|id| undefined[id] && defined[id]);
    // The overlap peaks whose sides the exploration does not join: each at the root of an
    // explored term (a peak below the root is one at the root of the explored subterm), with
    // the head of the equation at whose instance it is and the heads of the applications it
    // may make undefined (every head when the search is cut short): those the definedness of
    // the terms its sides reach rests on directly, and those in the values its two equations
    // bind.
    let every_head = (0..universe.definition.symbols.len())
        .map(|symbol| u32::try_from(symbol).unwrap())
        .collect::<BTreeSet<_>>();
    let mut peaks: Vec<Peak> = Vec::new();
    for from in &expanded {
        let steps = Rc::clone(&universe.steps[from]);
        for (index, first) in steps.iter().enumerate() {
            for second in &steps[index + 1..] {
                if first.to == second.to || !(first.path.is_empty() || second.path.is_empty()) {
                    continue;
                }
                let outer = if first.path.is_empty() { first } else { second };
                let (left, left_complete) = universe.reachable(first.to);
                let (right, right_complete) = universe.reachable(second.to);
                if !left.is_disjoint(&right) {
                    continue;
                }
                let mut exposed = BTreeSet::new();
                for id in left.iter().chain(&right) {
                    universe.exposed_heads(*id, &mut exposed);
                }
                if !(left_complete && right_complete) {
                    exposed.clone_from(&every_head);
                }
                // The equation instances of the two paths cannot all hold, so a value one of
                // them binds may be undefined: every application in the values the two steps
                // bind, and the steps their sides take, or in what those values reach. An
                // equation also binds its head's arguments, by membership; where one side is
                // proven defined and the other undefined, the instances of the two steps and of
                // the steps their sides take cannot all hold, so one of their redexes' arguments
                // may be undefined, and they count too.
                let contradict = |one: &HashSet<Id>, other: &HashSet<Id>| {
                    one.iter().any(|id| defined[*id as usize])
                        && other.iter().any(|id| undefined[*id as usize])
                };
                let arguments_bound = contradict(&left, &right) || contradict(&right, &left);
                let mut bound = BTreeSet::new();
                let mut values = first
                    .valuation
                    .iter()
                    .chain(&second.valuation)
                    .copied()
                    .collect::<Vec<_>>();
                if arguments_bound {
                    values.extend(&first.arguments);
                    values.extend(&second.arguments);
                }
                for id in left.iter().chain(&right) {
                    for step in universe
                        .steps
                        .get(id)
                        .into_iter()
                        .flat_map(|steps| steps.iter())
                    {
                        values.extend(&step.valuation);
                        if arguments_bound {
                            values.extend(&step.arguments);
                        }
                    }
                }
                for value in values {
                    let (reached, complete) = universe.reachable(value);
                    if !complete {
                        bound.clone_from(&every_head);
                        break;
                    }
                    for id in reached {
                        universe.heads(id, &HashSet::new(), &mut bound);
                    }
                }
                peaks.push(Peak {
                    head: outer.head,
                    exposed,
                    bound,
                });
            }
        }
    }
    // The documented assumption about equations of other heads: an equation of a total head
    // whose instance has an undefined right-hand side makes an application its left-hand side
    // holds below total symbols undefined (the total root is defined on defined arguments), and
    // the scan of that application does not read the other head's equations. Each such step at
    // the root of an explored term, with the heads it may make undefined that way.
    let mut held_below_total: Vec<(u32, BTreeSet<u32>)> = Vec::new();
    for from in &expanded {
        let Node::App(root, _) = &universe.nodes[*from as usize] else {
            continue;
        };
        if universe.is_constructor(*root) || !universe.is_total(*root) {
            continue;
        }
        for step in universe.steps[from].iter() {
            if step.path.is_empty() && undefined[step.to as usize] {
                let mut held = BTreeSet::new();
                for child in universe.children(*from) {
                    universe.exposed_heads(child, &mut held);
                }
                held_below_total.push((step.head, held));
            }
        }
    }
    // The applications that the left-hand side of one of their own head's conditional equations
    // matches. The certificate never reads one as a value: that equation is never set aside, and
    // a `requires` false at the match is not read as leaving the application free (the
    // withdrawn discharge did; `docs/compatibility.md`, "Anywhere rules"). Such an application
    // at an exposed position of a normal form the query reaches by steps, whose `\ceil` the
    // definedness walk asks, rests on none of the documented assumptions, so it excuses no
    // query: its obligation must stay. One below a partial head, or in a term the query's
    // evaluation passes through, still does: there the certificate, or the evaluation of the
    // enclosing equations, reads it.
    let mut conditional_applications = HashSet::new();
    for id in 1..count {
        let id = Id::try_from(id).unwrap();
        let Node::App(symbol, _) = universe.nodes[id as usize].clone() else {
            continue;
        };
        for equation in &definition.equations {
            let Pat::App(head, _) = &equation.lhs else {
                continue;
            };
            if equation.requires.is_some()
                && universe.symbols[head.as_str()] == symbol
                && universe.matches(&equation.lhs, id, &mut HashMap::new())
            {
                conditional_applications.insert(id);
                break;
            }
        }
    }
    let mut candidates = Vec::new();
    for query in queries {
        let id = universe.ground(query);
        if undefined[id as usize] && !candidates.contains(&id) {
            candidates.push(id);
        }
    }
    let mut others = (1..count)
        .map(|id| Id::try_from(id).unwrap())
        .filter(|id| {
            undefined[*id as usize]
                && universe.sizes[*id as usize] <= QUERY_SIZE
                && !candidates.contains(id)
        })
        .collect::<Vec<_>>();
    others.sort_by_key(|id| universe.sizes[*id as usize]);
    let undefined_terms = (1..count)
        .filter(|id| undefined[*id])
        .map(|id| universe.kore(Id::try_from(id).unwrap(), None))
        .collect::<HashSet<_>>();
    candidates.extend(others);
    let mut queries = Vec::new();
    for id in candidates.into_iter().take(QUERIES) {
        // The documented assumption: a peak at an instance of an equation of another head than
        // an application's, one of whose sides reaches that application's head, meets, and no
        // peak that does not meet binds a value in which the application occurs. The backend
        // evaluates the query first, so every application the query reaches counts.
        let (reached, complete) = universe.reachable(id);
        let mut heads = BTreeSet::new();
        if complete {
            let none = HashSet::new();
            for reached in &reached {
                // The backend asks the `\ceil` of the applications of the normal form it
                // evaluates the query to; an intermediate term's applications are only read by
                // the evaluation and the certificate.
                let normal = universe
                    .steps
                    .get(reached)
                    .is_some_and(|steps| steps.is_empty())
                    && !universe.loops.contains(reached);
                let skip = if normal {
                    &conditional_applications
                } else {
                    &none
                };
                universe.heads(*reached, skip, &mut heads);
            }
        } else {
            heads.clone_from(&every_head);
        }
        // A limit of the backend's evaluation, documented beside the assumption: it applies an
        // equation whose left-hand side matches syntactically, reading the applications in its
        // argument patterns as defined, although an undefined argument makes the instance state
        // nothing. A query whose evaluation may take such a step (a step of a term it reaches
        // with a redex argument in `U`) is not checked.
        let vacuous_step = !complete
            || reached.iter().any(|term| {
                universe.steps.get(term).is_some_and(|steps| {
                    steps.iter().any(|step| {
                        step.arguments
                            .iter()
                            .any(|argument| undefined[*argument as usize])
                    })
                })
            });
        let excused = vacuous_step
            || peaks.iter().any(|peak| {
                heads.iter().any(|application| {
                    (*application != peak.head && peak.exposed.contains(application))
                        || peak.bound.contains(application)
                })
            })
            || held_below_total.iter().any(|(head, held)| {
                heads
                    .iter()
                    .any(|application| application != head && held.contains(application))
            });
        let sort = universe.sort_of(id);
        let terminates = universe.terminates(id);
        queries.push(Query {
            term: universe.kore(id, None),
            sort: sort.clone(),
            excused,
            terminates,
        });
        // Generalize one constructor subterm at a time: the instance at that value is `id`.
        let mut pure_subterms = BTreeSet::new();
        let mut stack = universe.children(id);
        while let Some(subterm) = stack.pop() {
            if pure[subterm as usize] {
                pure_subterms.insert(subterm);
            } else {
                stack.extend(universe.children(subterm));
            }
        }
        for (index, subterm) in pure_subterms.into_iter().take(2).enumerate() {
            let variable = format!("Q{index}:{}", universe.sort_of(subterm));
            // An equation that matches the generalization matches its instance `id`, so its
            // evaluation ends where `id`'s does.
            queries.push(Query {
                term: universe.kore(id, Some((subterm, &variable))),
                sort: sort.clone(),
                excused,
                terminates,
            });
        }
    }
    Verdicts {
        universe_size: count,
        inconsistent,
        queries,
        undefined: undefined_terms,
    }
}

// ---------------------------------------------------------------------------------------------
// The backend's claims.

/// The claims the backend makes about `query` that the oracle refutes, under `definition`.
fn refuted_claims(definition: &BackendDefinition, query: &Query) -> Result<(), String> {
    let ceil = format!(r"\ceil{{{0}, {0}}}({1})", query.sort, query.term);
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        let term = definition
            .internalize_term(&parse_pattern(&query.term).expect("the term parses"), &[])
            .expect("the term internalizes");
        if definition.instance_normal(&term).is_some() {
            return Err(format!("{} is instance-normal", query.term));
        }
        if !query.terminates {
            // Simplifying `\ceil` evaluates the term, which need not end.
            return Ok(());
        }
        let syntax = parse_pattern(&ceil).expect("the query parses");
        let (predicate, _) = definition
            .admit_unverified(&syntax, &[])
            .internalize_predicate()
            .expect("the query internalizes");
        // A small budget for the steps that are not ground evaluation: an exhausted budget is
        // an error, which claims nothing.
        let simplified = simplify_predicate_with_solver(
            definition,
            &predicate,
            &[],
            SimplificationOptions {
                max_iterations: 16,
                ..SimplificationOptions::default()
            },
            &NoSolver,
        );
        match simplified {
            Ok(Ok(Predicate::True)) => return Err(format!("{ceil} simplifies to \\top")),
            Ok(_) => {}
            // A stop (here, the stack guard) claims nothing.
            Err(stop) => {
                stop.into_cause();
            }
        }
        Ok(())
    }));
    outcome.unwrap_or_else(|panic| {
        let message = panic
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| panic.downcast_ref::<&str>().map(|text| (*text).to_string()))
            .unwrap_or_default();
        Err(format!("{ceil} panicked: {message}"))
    })
}

#[derive(Debug, Default)]
struct Tally {
    definitions: usize,
    rejected: usize,
    inconsistent: usize,
    universe: usize,
    checked: usize,
    /// Of the checked queries, those whose `\ceil` was simplified ([`Query::terminates`]).
    evaluated: usize,
    excused: usize,
    failures: Vec<String>,
}

/// Runs the oracle on `definition` and checks every query under both bounds.
fn check_definition(
    label: &str,
    definition: &Definition,
    extra: &[Pat],
    queries: &[Pat],
    rng: &mut Rng,
) -> (Verdicts, Tally) {
    let mut tally = Tally {
        definitions: 1,
        ..Tally::default()
    };
    let verbose = std::env::var_os("KRUST_DEFINEDNESS_ORACLE_VERBOSE").is_some();
    if verbose {
        eprintln!("{label}: oracle\n{}", describe(definition));
    }
    if std::env::var_os("KRUST_DEFINEDNESS_ORACLE_KORE").is_some() {
        eprintln!("{}", definition.kore());
    }
    let verdicts = oracle(definition, extra, queries, rng);
    tally.universe = verdicts.universe_size;
    if verdicts.inconsistent {
        tally.inconsistent = 1;
        return (verdicts, tally);
    }
    let source = definition.kore();
    for (mode, bounds) in [("default", Bounds::DEFAULT), ("minimal", MINIMAL)] {
        with_bounds(bounds, || {
            let Ok(syntax) = parse_definition(&source) else {
                tally.rejected += 1;
                return;
            };
            let Ok(backend) = BackendDefinition::internalize(&syntax, "MAIN") else {
                tally.rejected += 1;
                return;
            };
            for query in &verdicts.queries {
                if verbose {
                    eprintln!("{label} ({mode} bounds): {}", query.term);
                }
                if query.excused {
                    tally.excused += 1;
                    continue;
                }
                tally.checked += 1;
                tally.evaluated += usize::from(query.terminates);
                if let Err(failure) = refuted_claims(&backend, query) {
                    tally.failures.push(format!(
                        "{label} ({mode} bounds): {failure}\n  definition:\n{}",
                        describe(definition)
                    ));
                }
            }
        });
    }
    (verdicts, tally)
}

fn describe(definition: &Definition) -> String {
    let mut text = String::new();
    for symbol in &definition.symbols {
        writeln!(
            text,
            "    {} {}({}) : {}",
            match (symbol.constructor, symbol.totality) {
                (true, _) => "constructor",
                (false, Totality::Production) => "head",
                (false, Totality::Head) => "total head",
                (false, Totality::Function) => "total function",
            },
            symbol.name,
            symbol.arguments.join(", "),
            symbol.result
        )
        .unwrap();
    }
    for equation in &definition.equations {
        write!(
            text,
            "    {} = {}",
            show(&equation.lhs),
            show(&equation.rhs)
        )
        .unwrap();
        if let Some(requires) = &equation.requires {
            write!(
                text,
                " requires {} {} {}",
                requires.variable,
                match requires.comparison {
                    Comparison::Eq => "==Int",
                    Comparison::Lt => "<Int",
                },
                requires.value
            )
            .unwrap();
        }
        text.push('\n');
    }
    text
}

fn show(pattern: &Pat) -> String {
    match pattern {
        Pat::Var(name, _) => name.clone(),
        Pat::App(name, arguments) if arguments.is_empty() => name.clone(),
        Pat::App(name, arguments) => format!(
            "{name}({})",
            arguments.iter().map(show).collect::<Vec<_>>().join(", ")
        ),
        Pat::Int(value) => value.to_string(),
        Pat::Inj(from, to, pattern) => format!("inj{{{from},{to}}}({})", show(pattern)),
        Pat::Div(left, right) => format!("{} /Int {}", show(left), show(right)),
    }
}

impl Tally {
    fn add(&mut self, other: Self) {
        self.definitions += other.definitions;
        self.rejected += other.rejected;
        self.inconsistent += other.inconsistent;
        self.universe += other.universe;
        self.checked += other.checked;
        self.evaluated += other.evaluated;
        self.excused += other.excused;
        self.failures.extend(other.failures);
    }
}

// ---------------------------------------------------------------------------------------------
// Random definitions.

/// SplitMix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut mixed = self.0;
        mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        mixed ^ (mixed >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % u64::try_from(bound).unwrap()).unwrap()
    }

    fn percent(&mut self, chance: usize) -> bool {
        self.below(100) < chance
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

const A_VARIABLES: [&str; 3] = ["VarX", "VarY", "VarZ"];
const INT_VARIABLES: [&str; 2] = ["VarI", "VarJ"];

struct Generator<'r> {
    rng: &'r mut Rng,
    /// The heads that have equations: value productions and total equation heads.
    heads: Vec<Symbol>,
    /// Total functions, which have no equations and occur in right-hand sides only.
    functions: Vec<Symbol>,
}

impl Generator<'_> {
    fn heads_of(&self, sort: &str) -> Vec<Symbol> {
        self.heads
            .iter()
            .filter(|head| head.result == sort)
            .cloned()
            .collect()
    }

    fn functions_of(&self, sort: &str) -> Vec<Symbol> {
        self.functions
            .iter()
            .filter(|function| function.result == sort)
            .cloned()
            .collect()
    }

    fn head_application(
        &mut self,
        head: &Symbol,
        depth: usize,
        left: bool,
        scope: &BTreeMap<String, String>,
    ) -> Pat {
        let arguments = head
            .arguments
            .iter()
            .map(|sort| {
                if left {
                    self.left(sort, depth - 1)
                } else {
                    self.right(sort, depth - 1, scope)
                }
            })
            .collect();
        app(&head.name, arguments)
    }

    /// A left-hand side argument of sort `sort`.
    fn left(&mut self, sort: &str, depth: usize) -> Pat {
        let nested = self.heads_of(sort);
        if depth > 0 && !nested.is_empty() && self.rng.percent(15) {
            let head = self.rng.pick(&nested).clone();
            return self.head_application(&head, depth, true, &BTreeMap::new());
        }
        match sort {
            "Int" => {
                if self.rng.percent(50) {
                    var(self.rng.pick::<&str>(&INT_VARIABLES), "Int")
                } else {
                    int(i64::try_from(self.rng.below(4)).unwrap())
                }
            }
            _ => {
                if self.rng.percent(40) {
                    return var(self.rng.pick::<&str>(&A_VARIABLES), "A");
                }
                self.constructor_term(depth, |generator, sort, depth| generator.left(sort, depth))
            }
        }
    }

    fn constructor_term(
        &mut self,
        depth: usize,
        mut argument: impl FnMut(&mut Self, &str, usize) -> Pat,
    ) -> Pat {
        if depth == 0 || self.rng.percent(30) {
            return cons(self.rng.pick::<&str>(&["c", "d"]));
        }
        match self.rng.below(4) {
            0 => app("n", vec![argument(self, "A", depth - 1)]),
            1 => app("k", vec![argument(self, "A", depth - 1)]),
            2 => app(
                "j",
                vec![
                    argument(self, "A", depth - 1),
                    argument(self, "A", depth - 1),
                ],
            ),
            _ => app("m", vec![argument(self, "Int", depth - 1)]),
        }
    }

    /// A right-hand side term of sort `sort` over the variables `scope`.
    fn right(&mut self, sort: &str, depth: usize, scope: &BTreeMap<String, String>) -> Pat {
        let in_scope = scope
            .iter()
            .filter(|(_, variable_sort)| *variable_sort == sort)
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let heads = self.heads_of(sort);
        if depth > 0 && !heads.is_empty() && self.rng.percent(30) {
            let head = self.rng.pick(&heads).clone();
            return self.head_application(&head, depth, false, scope);
        }
        let functions = self.functions_of(sort);
        if depth > 0 && !functions.is_empty() && self.rng.percent(15) {
            let function = self.rng.pick(&functions).clone();
            return self.head_application(&function, depth, false, scope);
        }
        match sort {
            "S" => {
                if depth > 0 && self.rng.percent(40) {
                    let dividend = self.right("Int", depth - 1, scope);
                    let divisor = self.divisor(scope);
                    app("mk", vec![div(dividend, divisor)])
                } else {
                    let argument = self.right("Int", depth.saturating_sub(1), scope);
                    app("mk", vec![argument])
                }
            }
            "Int" => {
                if !in_scope.is_empty() && self.rng.percent(50) {
                    var(self.rng.pick(&in_scope).as_str(), "Int")
                } else if depth > 0 && self.rng.percent(10) {
                    let dividend = self.right("Int", depth - 1, scope);
                    let divisor = self.divisor(scope);
                    div(dividend, divisor)
                } else {
                    int(i64::try_from(self.rng.below(4)).unwrap())
                }
            }
            _ => {
                if !in_scope.is_empty() && self.rng.percent(35) {
                    return var(self.rng.pick(&in_scope).as_str(), "A");
                }
                self.constructor_term(depth, |generator, sort, depth| {
                    generator.right(sort, depth, scope)
                })
            }
        }
    }

    fn divisor(&mut self, scope: &BTreeMap<String, String>) -> Pat {
        let integers = scope
            .iter()
            .filter(|(_, sort)| *sort == "Int")
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        if integers.is_empty() || self.rng.percent(60) {
            int(0)
        } else {
            var(self.rng.pick(&integers).as_str(), "Int")
        }
    }
}

fn random_definition(rng: &mut Rng) -> Definition {
    let names = ["f", "g", "h", "q"];
    let count = 2 + rng.below(3);
    let mut heads = Vec::new();
    for name in &names[..count] {
        let result = match rng.below(100) {
            0..40 => "S",
            40..85 => "A",
            _ => "Int",
        };
        let arity = match rng.below(100) {
            0..40 => 1,
            40..85 => 2,
            _ => 3,
        };
        let arguments = (0..arity)
            .map(|_| if rng.percent(70) { "A" } else { "Int" }.to_string())
            .collect();
        heads.push(Symbol {
            name: (*name).into(),
            arguments,
            result: result.into(),
            constructor: false,
            totality: Totality::Production,
        });
    }
    // Total symbols, which pass definedness to their arguments: an `anywhere` head `e : A -> A`
    // (which may have equations) and a function `sz : A -> Int` (which has none).
    let mut functions = Vec::new();
    if rng.percent(40) {
        heads.push(Symbol {
            name: "e".into(),
            arguments: vec!["A".into()],
            result: "A".into(),
            constructor: false,
            totality: Totality::Head,
        });
    }
    if rng.percent(30) {
        functions.push(Symbol {
            name: "sz".into(),
            arguments: vec!["A".into()],
            result: "Int".into(),
            constructor: false,
            totality: Totality::Function,
        });
    }
    let mut definition = Definition::new(&["A"])
        .constructor("c", &[], "A")
        .constructor("d", &[], "A")
        .constructor("n", &["A"], "A")
        .constructor("k", &["A"], "A")
        .constructor("j", &["A", "A"], "A")
        .constructor("m", &["Int"], "A");
    definition.symbols.extend(heads.iter().cloned());
    definition.symbols.extend(functions.iter().cloned());
    let mut generator = Generator {
        rng,
        heads,
        functions,
    };
    let equations = 2 + generator.rng.below(5);
    let mut previous: Option<Symbol> = None;
    for _ in 0..equations {
        let head = match &previous {
            Some(head) if generator.rng.percent(50) => head.clone(),
            _ => generator.rng.pick(&generator.heads).clone(),
        };
        let lhs = generator.head_application(&head, 3, true, &BTreeMap::new());
        let mut scope = BTreeMap::new();
        pattern_variables(&lhs, &mut scope);
        let rhs = generator.right(&head.result, 3, &scope);
        let integers = scope
            .iter()
            .filter(|(_, sort)| *sort == "Int")
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        let requires = (!integers.is_empty() && generator.rng.percent(35)).then(|| Requires {
            comparison: if generator.rng.percent(50) {
                Comparison::Eq
            } else {
                Comparison::Lt
            },
            variable: generator.rng.pick(&integers).clone(),
            value: i64::try_from(generator.rng.below(4)).unwrap(),
        });
        definition.equations.push(Equation { lhs, rhs, requires });
        previous = Some(head);
    }
    if generator.rng.percent(50) {
        plant_held_conditional(&mut generator, &mut definition);
    }
    definition
}

/// Plants review 7 F1's shape: a value production `p` with a conditional equation (added when
/// `p` has none), and an equation whose left-hand side holds, below its root, an instance of
/// that equation's left-hand side with the `requires` variable bound to a literal; its root is
/// another head (often a total one, when the definition has it) or `p` itself, and its
/// right-hand side is often undefined. Under such an equation the theory can make the instance
/// undefined while `p`'s own `requires` is false there.
fn plant_held_conditional(generator: &mut Generator<'_>, definition: &mut Definition) {
    let productions = generator
        .heads
        .iter()
        .filter(|head| head.totality == Totality::Production && head.result != "S")
        .cloned()
        .collect::<Vec<_>>();
    if productions.is_empty() {
        return;
    }
    let held = generator.rng.pick(&productions).clone();
    let existing = definition
        .equations
        .iter()
        .find(|equation| {
            equation.requires.is_some()
                && matches!(&equation.lhs, Pat::App(name, _) if *name == held.name)
        })
        .cloned();
    let conditional = if let Some(existing) = existing {
        existing
    } else {
        let arguments = held
            .arguments
            .iter()
            .enumerate()
            .map(|(index, sort)| match (index, sort.as_str()) {
                (0, "Int") => int_var("VarI"),
                (0, _) => app("m", vec![int_var("VarI")]),
                _ => generator.left(sort, 2),
            })
            .collect();
        let lhs = app(&held.name, arguments);
        let mut scope = BTreeMap::new();
        pattern_variables(&lhs, &mut scope);
        let rhs = generator.right(&held.result, 2, &scope);
        let equation = Equation {
            lhs,
            rhs,
            requires: Some(Requires {
                comparison: if generator.rng.percent(50) {
                    Comparison::Eq
                } else {
                    Comparison::Lt
                },
                variable: "VarI".into(),
                value: i64::try_from(generator.rng.below(4)).unwrap(),
            }),
        };
        definition.equations.push(equation.clone());
        equation
    };
    let variable = &conditional
        .requires
        .as_ref()
        .expect("the equation is conditional")
        .variable;
    let literal = int(i64::try_from(generator.rng.below(4)).unwrap());
    let instance = substituted(&conditional.lhs, variable, &literal);
    let outers = generator
        .heads
        .iter()
        .filter(|head| head.arguments.contains(&held.result))
        .cloned()
        .collect::<Vec<_>>();
    let total = outers
        .iter()
        .filter(|head| head.totality != Totality::Production)
        .cloned()
        .collect::<Vec<_>>();
    let outer = if !total.is_empty() && generator.rng.percent(40) {
        generator.rng.pick(&total).clone()
    } else if outers.is_empty() {
        return;
    } else {
        generator.rng.pick(&outers).clone()
    };
    let positions = (0..outer.arguments.len())
        .filter(|index| outer.arguments[*index] == held.result)
        .collect::<Vec<_>>();
    let position = *generator.rng.pick(&positions);
    let arguments = outer
        .arguments
        .iter()
        .enumerate()
        .map(|(index, sort)| {
            if index == position {
                instance.clone()
            } else {
                generator.left(sort, 1)
            }
        })
        .collect();
    let lhs = app(&outer.name, arguments);
    let rhs = if generator.rng.percent(60) {
        match outer.result.as_str() {
            "S" => undefined(),
            "Int" => div(int(1), int(0)),
            _ => app("m", vec![div(int(1), int(0))]),
        }
    } else {
        let mut scope = BTreeMap::new();
        pattern_variables(&lhs, &mut scope);
        generator.right(&outer.result, 2, &scope)
    };
    definition.equations.push(Equation {
        lhs,
        rhs,
        requires: None,
    });
}

/// `pattern` with the variable `name` replaced by `replacement`.
fn substituted(pattern: &Pat, name: &str, replacement: &Pat) -> Pat {
    match pattern {
        Pat::Var(variable, _) if variable == name => replacement.clone(),
        Pat::Var(..) | Pat::Int(_) => pattern.clone(),
        Pat::App(symbol, arguments) => Pat::App(
            symbol.clone(),
            arguments
                .iter()
                .map(|argument| substituted(argument, name, replacement))
                .collect(),
        ),
        Pat::Inj(from, to, inner) => Pat::Inj(
            from.clone(),
            to.clone(),
            Box::new(substituted(inner, name, replacement)),
        ),
        Pat::Div(left, right) => Pat::Div(
            Box::new(substituted(left, name, replacement)),
            Box::new(substituted(right, name, replacement)),
        ),
    }
}

fn environment(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

/// Runs `body` on a thread with a large stack: deep simplifications must not abort the run.
fn on_large_stack(body: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(512 << 20)
        .spawn(body)
        .expect("the test thread starts")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
}

#[test]
fn random_definitions_claim_no_definedness_the_axioms_refute() {
    on_large_stack(|| {
        let cases = environment("KRUST_DEFINEDNESS_ORACLE_CASES", DEFAULT_CASES);
        let seed = environment("KRUST_DEFINEDNESS_ORACLE_SEED", DEFAULT_SEED);
        let first = environment("KRUST_DEFINEDNESS_ORACLE_FIRST", 0);
        let verbose = std::env::var_os("KRUST_DEFINEDNESS_ORACLE_VERBOSE").is_some();
        let mut total = Tally::default();
        for case in first..first + cases {
            let started = std::time::Instant::now();
            let mut rng = Rng(seed ^ case.wrapping_mul(0x9e37_79b9_7f4a_7c15));
            let definition = random_definition(&mut rng);
            let (_, tally) = check_definition(
                &format!("seed {seed:#x} case {case}"),
                &definition,
                &[],
                &[],
                &mut rng,
            );
            total.add(tally);
            if verbose {
                eprintln!("case {case}: {:?}", started.elapsed());
            }
            if total.failures.len() >= 20 {
                break;
            }
        }
        eprintln!(
            "definedness oracle: {} definitions ({} rejected by internalization, {} inconsistent), {} terms explored, {} undefined terms checked ({} also by \\ceil), {} excused by the documented assumption, {} failures",
            total.definitions,
            total.rejected,
            total.inconsistent,
            total.universe,
            total.checked,
            total.evaluated,
            total.excused,
            total.failures.len()
        );
        assert!(total.failures.is_empty(), "{}", total.failures.join("\n"));
    });
}

// ---------------------------------------------------------------------------------------------
// The reviewers' probes.

/// One probe: a definition, terms to seed the exploration with (the start of the conversion
/// that makes the query undefined), the queries the oracle must prove undefined, and whether
/// the documented cross-head assumption excuses them.
struct Probe {
    name: String,
    definition: Definition,
    seeds: Vec<Pat>,
    undefined: Vec<Pat>,
    /// Terms the oracle must not prove undefined: some model of the axioms defines them.
    free: Vec<Pat>,
    excused: bool,
}

fn probe(name: &str, definition: Definition, seeds: Vec<Pat>, undefined: Vec<Pat>) -> Probe {
    Probe {
        name: name.into(),
        definition,
        seeds,
        undefined,
        free: Vec::new(),
        excused: false,
    }
}

fn int_var(name: &str) -> Pat {
    var(name, "Int")
}

#[allow(
    clippy::too_many_lines,
    reason = "one probe per reviewed counterexample"
)]
fn probes() -> Vec<Probe> {
    let mut probes = Vec::new();
    // Review 1, F1 and F2: `h(3) = h(1)`, `w(h(X)) = mk(X /Int 0) requires X ==Int 3`, and the
    // unconditional `w(h(3)) = mk(1 /Int 0)`.
    let review1 = Definition::new(&["H"])
        .head("h", &["Int"], "H")
        .head("w", &["H"], "S")
        .equation(app("h", vec![int(3)]), app("h", vec![int(1)]));
    probes.push(probe(
        "review 1 F1",
        review1.clone().conditional(
            app("w", vec![app("h", vec![int_var("VarX")])]),
            app("mk", vec![div(int_var("VarX"), int(0))]),
            requires_eq("VarX", 3),
        ),
        vec![],
        vec![
            app("w", vec![app("h", vec![int(1)])]),
            app("w", vec![app("h", vec![int(3)])]),
        ],
    ));
    probes.push(probe(
        "review 1 F2",
        review1.equation(app("w", vec![app("h", vec![int(3)])]), undefined()),
        vec![],
        vec![app("w", vec![app("h", vec![int(1)])])],
    ));
    // Review 2, F1: sorts `B < A < T`; `h(inj{A,T}(X)) = k(X)`, `w(h(inj{B,T}(b0))) = mk(1 /Int 0)`.
    probes.push(probe(
        "review 2 F1",
        Definition::new(&["B", "A", "T", "H"])
            .subsort("B", "A")
            .subsort("A", "T")
            .subsort("B", "T")
            .constructor("b0", &[], "B")
            .constructor("k", &["A"], "H")
            .head("h", &["T"], "H")
            .head("w", &["H"], "S")
            .equation(
                app("h", vec![inj("A", "T", var("VarX", "A"))]),
                app("k", vec![var("VarX", "A")]),
            )
            .equation(
                app("w", vec![app("h", vec![inj("B", "T", cons("b0"))])]),
                undefined(),
            ),
        vec![],
        vec![app("w", vec![app("k", vec![inj("B", "A", cons("b0"))])])],
    ));
    // Round 3: sorts `C < A < T`, `C < B < T`; `g() = inj{C,B}(c0)`.
    probes.push(probe(
        "round 3 common subsort",
        Definition::new(&["C", "A", "B", "T", "H"])
            .subsort("C", "A")
            .subsort("A", "T")
            .subsort("C", "B")
            .subsort("B", "T")
            .subsort("C", "T")
            .constructor("c0", &[], "C")
            .constructor("k", &["A"], "H")
            .head("g", &[], "B")
            .head("h", &["T"], "H")
            .head("w", &["H"], "S")
            .equation(
                app("h", vec![inj("A", "T", var("VarX", "A"))]),
                app("k", vec![var("VarX", "A")]),
            )
            .equation(cons("g"), inj("C", "B", cons("c0")))
            .equation(
                app("w", vec![app("h", vec![inj("B", "T", cons("g"))])]),
                undefined(),
            ),
        vec![],
        vec![app("w", vec![app("k", vec![inj("C", "A", cons("c0"))])])],
    ));
    // Review 2, F2: `g(5) = f(0)`, `h(g(X)) = k2(X)`, `w(h(f(0))) = mk(1 /Int 0)`. `f` is a
    // total function: were `f(0)` undefined, the `g` and `w` equations, which bind their
    // arguments by membership, would state nothing at `g(5)` and `h(f(0))`, and `w(k2(5))`
    // would be undefined only in the models where `f(0)` is defined.
    probes.push(probe(
        "review 2 F2",
        Definition::new(&["G", "H"])
            .constructor("k2", &["Int"], "H")
            .total_function("f", &["Int"], "G")
            .head("g", &["Int"], "G")
            .head("h", &["G"], "H")
            .head("w", &["H"], "S")
            .equation(app("g", vec![int(5)]), app("f", vec![int(0)]))
            .equation(
                app("h", vec![app("g", vec![int_var("VarX")])]),
                app("k2", vec![int_var("VarX")]),
            )
            .equation(
                app("w", vec![app("h", vec![app("f", vec![int(0)])])]),
                undefined(),
            ),
        vec![app("w", vec![app("h", vec![app("g", vec![int(5)])])])],
        vec![app("w", vec![app("k2", vec![int(5)])])],
    ));
    // Review 2, F3: `f(f(inj{K,F}(k(X)))) = c` must not recurse without bound.
    probes.push(probe(
        "review 2 F3",
        Definition::new(&["K", "F"])
            .subsort("K", "F")
            .constructor("k", &["F"], "K")
            .constructor("c", &[], "F")
            .head("f", &["F"], "F")
            .equation(
                app(
                    "f",
                    vec![app(
                        "f",
                        vec![inj("K", "F", app("k", vec![var("VarX", "F")]))],
                    )],
                ),
                cons("c"),
            ),
        vec![app("f", vec![inj("K", "F", app("k", vec![cons("c")]))])],
        vec![],
    ));
    // Review 3, F1, and my round-4 counterexample: `g(5) = c1` and two `f` equations.
    let review3 = Definition::new(&["G"])
        .constructor("c1", &[], "G")
        .constructor("c2", &[], "G")
        .constructor("c3", &[], "G")
        .head("g", &["Int"], "G")
        .head("f", &["G", "Int"], "S")
        .equation(app("g", vec![int(5)]), cons("c1"));
    let z = || int_var("VarZ");
    probes.push(probe(
        "review 3 F1",
        review3
            .clone()
            .equation(
                app("f", vec![cons("c1"), z()]),
                app("f", vec![cons("c2"), z()]),
            )
            .equation(
                app("f", vec![app("g", vec![int_var("VarX")]), z()]),
                undefined(),
            ),
        vec![app("f", vec![app("g", vec![int(5)]), int(0)])],
        vec![app("f", vec![cons("c2"), int(0)])],
    ));
    probes.push(probe(
        "round 4 own root step",
        review3
            .equation(
                app("f", vec![app("g", vec![int_var("VarX")]), z()]),
                app("f", vec![cons("c2"), z()]),
            )
            .equation(app("f", vec![cons("c1"), z()]), undefined()),
        vec![app("f", vec![app("g", vec![int(5)]), int(0)])],
        vec![app("f", vec![cons("c2"), int(0)])],
    ));
    // Review 3, F2: `f(X, Z) = mk(X /Int 0) requires X ==Int 3` and `f(3, Z) = f(1, Z)`.
    probes.push(probe(
        "review 3 F2",
        Definition::new(&[])
            .head("f", &["Int", "Int"], "S")
            .equation(app("f", vec![int(3), z()]), app("f", vec![int(1), z()]))
            .conditional(
                app("f", vec![int_var("VarX"), z()]),
                app("mk", vec![div(int_var("VarX"), int(0))]),
                requires_eq("VarX", 3),
            ),
        vec![],
        vec![app("f", vec![int(1), int(0)])],
    ));
    // Review 4, F1: `O: f(e(Y), W) = f(d(Y), c)`, `P: f(V, k(Y)) = f(d(Y), c)`, and either
    // `f(d(X), c) = mk(X /Int 0) requires X ==Int 3` or `f(d(3), c) = mk(1 /Int 0)`; `P`'s
    // variable named like `O`'s or not.
    for second in ["VarY", "VarU"] {
        let review4 = Definition::new(&["A", "T"])
            .constructor("e", &["Int"], "A")
            .constructor("d", &["Int"], "A")
            .constructor("k", &["Int"], "T")
            .constructor("c", &[], "T")
            .head("f", &["A", "T"], "S")
            .equation(
                app("f", vec![app("e", vec![int_var("VarY")]), var("VarW", "T")]),
                app("f", vec![app("d", vec![int_var("VarY")]), cons("c")]),
            )
            .equation(
                app("f", vec![var("VarV", "A"), app("k", vec![int_var(second)])]),
                app("f", vec![app("d", vec![int_var(second)]), cons("c")]),
            );
        let seeds = vec![app(
            "f",
            vec![app("e", vec![int(1)]), app("k", vec![int(3)])],
        )];
        let query = vec![app("f", vec![app("d", vec![int(1)]), cons("c")])];
        probes.push(probe(
            &format!("review 4 F1 discharge ({second})"),
            review4.clone().conditional(
                app("f", vec![app("d", vec![int_var("VarX")]), cons("c")]),
                app("mk", vec![div(int_var("VarX"), int(0))]),
                requires_eq("VarX", 3),
            ),
            seeds.clone(),
            query.clone(),
        ));
        probes.push(probe(
            &format!("review 4 F1 instance normality ({second})"),
            review4.equation(
                app("f", vec![app("d", vec![int(3)]), cons("c")]),
                undefined(),
            ),
            seeds,
            query,
        ));
    }
    // Round 6, from the random run (seed 0x5eed0006, case 115): `q(q(Y, J), J) = q(q(c, J), J)`
    // overlaps itself below its root, so each round of the pattern facts builds larger overlap
    // representatives from the last; without a bound on their work the rounds exhaust memory.
    probes.push(probe(
        "round 6 self overlap",
        Definition::new(&["A"])
            .constructor("c", &[], "A")
            .constructor("d", &[], "A")
            .constructor("k", &["A"], "A")
            .constructor("j", &["A", "A"], "A")
            .constructor("m", &["Int"], "A")
            .head("g", &["A"], "S")
            .head("q", &["A", "Int"], "A")
            .equation(
                app("g", vec![app("m", vec![int(2)])]),
                app("mk", vec![div(int(3), int(0))]),
            )
            .equation(
                app(
                    "g",
                    vec![app(
                        "q",
                        vec![app("j", vec![cons("c"), cons("c")]), int_var("VarI")],
                    )],
                ),
                app("g", vec![app("k", vec![app("q", vec![cons("d"), int(2)])])]),
            )
            .equation(app("q", vec![cons("d"), int(2)]), app("m", vec![int(2)]))
            .equation(
                app(
                    "q",
                    vec![
                        app("q", vec![var("VarY", "A"), int_var("VarJ")]),
                        int_var("VarJ"),
                    ],
                ),
                app(
                    "q",
                    vec![app("q", vec![cons("c"), int_var("VarJ")]), int_var("VarJ")],
                ),
            ),
        vec![],
        vec![app("g", vec![app("m", vec![int(2)])])],
    ));
    // Round 6, from the random run (seed 0x5eed0006, case 482): `h(q(3, Y)) = 1 /Int 0` and
    // `h(X) = 3` do not meet at `h(q(3, c))`, so the value `q(3, c)` that `h(X) = 3` binds there
    // is undefined, and so is its normal form `g(d)`; the documented assumption, excused.
    probes.push(Probe {
        excused: true,
        ..probe(
            "round 6 bound value",
            Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .head("g", &["A"], "A")
                .head("h", &["A"], "Int")
                .head("q", &["Int", "A"], "A")
                .equation(
                    app("h", vec![app("q", vec![int(3), var("VarY", "A")])]),
                    div(int(1), int(0)),
                )
                .equation(app("h", vec![var("VarX", "A")]), int(3))
                .equation(
                    app("q", vec![int_var("VarI"), var("VarX", "A")]),
                    app("g", vec![cons("d")]),
                ),
            vec![app("h", vec![app("q", vec![int(3), cons("c")])])],
            vec![app("h", vec![app("g", vec![cons("d")])])],
        )
    });
    // Review 4, F2: the cross-head example of `docs/compatibility.md` with a conditional `wrap`
    // equation. `wrap(1)` is undefined through the peak of the `h` equations at `h(g(5))`; its
    // own conditional equation matches it (with a false `requires`), so the peak assumption
    // does not excuse it, and it keeps its obligation.
    probes.push(Probe {
        excused: false,
        ..probe(
            "review 4 F2",
            Definition::new(&["G"])
                .constructor("c1", &[], "G")
                .head("wrap", &["Int"], "S")
                .head("g", &["Int"], "G")
                .head("h", &["G"], "S")
                .conditional(
                    app("wrap", vec![int_var("VarX")]),
                    app("mk", vec![div(int_var("VarX"), int(0))]),
                    requires_eq("VarX", 0),
                )
                .equation(app("g", vec![int(5)]), cons("c1"))
                .equation(app("h", vec![cons("c1")]), app("wrap", vec![int(1)]))
                .equation(app("h", vec![app("g", vec![int_var("VarX")])]), undefined()),
            vec![app("h", vec![app("g", vec![int(5)])])],
            vec![app("wrap", vec![int(1)])],
        )
    });
    // Round 5 (mine): reducts that keep a variable narrowing leaves unbound, chained and
    // composed, named like the `f` equation's or not.
    for name in ["VarZ", "VarU"] {
        let chained = |first: Pat| {
            Definition::new(&["A"])
                .constructor("k", &["A"], "A")
                .constructor("s", &["A"], "A")
                .constructor("m", &["A"], "A")
                .constructor("m2", &["A"], "A")
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .head("p", &["A", "A"], "A")
                .head("h", &["A", "A"], "A")
                .head("q", &["A", "A", "A"], "A")
                .head("v", &["A"], "A")
                .head("f", &["A"], "S")
                .equation(
                    app("q", vec![first, var("VarX", "A"), var("VarX", "A")]),
                    cons("c"),
                )
                .equation(
                    app(
                        "f",
                        vec![app(
                            "p",
                            vec![var("VarA", "A"), app("s", vec![var("VarZ", "A")])],
                        )],
                    ),
                    undefined(),
                )
        };
        let subject = app("f", vec![app("m", vec![app("m2", vec![cons("c")])])]);
        probes.push(probe(
            &format!("round 5 chained ({name})"),
            chained(cons("c"))
                .equation(
                    app(
                        "p",
                        vec![app("k", vec![var("VarY", "A")]), var("VarV", "A")],
                    ),
                    app(
                        "m",
                        vec![app("h", vec![var("VarY", "A"), var("VarV", "A")])],
                    ),
                )
                .equation(
                    app("h", vec![app("k", vec![var(name, "A")]), var("VarV", "A")]),
                    app(
                        "m2",
                        vec![app(
                            "q",
                            vec![var(name, "A"), var("VarV", "A"), app("s", vec![cons("d")])],
                        )],
                    ),
                ),
            vec![app(
                "f",
                vec![app(
                    "p",
                    vec![
                        app("k", vec![app("k", vec![cons("c")])]),
                        app("s", vec![cons("d")]),
                    ],
                )],
            )],
            vec![subject.clone()],
        ));
        probes.push(probe(
            &format!("round 5 composed ({name})"),
            chained(app("k", vec![cons("c")]))
                .equation(
                    app(
                        "p",
                        vec![app("k", vec![var("VarY", "A")]), var("VarV", "A")],
                    ),
                    app("m", vec![app("h", vec![cons("c"), var("VarV", "A")])]),
                )
                .equation(
                    app(
                        "h",
                        vec![app("v", vec![var("VarX", "A")]), var("VarV", "A")],
                    ),
                    app(
                        "m2",
                        vec![app(
                            "q",
                            vec![
                                var("VarX", "A"),
                                var("VarV", "A"),
                                app("s", vec![cons("d")]),
                            ],
                        )],
                    ),
                )
                .equation(app("v", vec![app("k", vec![var(name, "A")])]), cons("c")),
            vec![
                app(
                    "f",
                    vec![app(
                        "p",
                        vec![app("k", vec![cons("c")]), app("s", vec![cons("d")])],
                    )],
                ),
                app(
                    "f",
                    vec![app(
                        "m",
                        vec![app(
                            "h",
                            vec![
                                app("v", vec![app("k", vec![cons("c")])]),
                                app("s", vec![cons("d")]),
                            ],
                        )],
                    )],
                ),
            ],
            vec![subject],
        ));
    }
    // Review 5, F1: `canonical` names. `H`'s first variable named like `G`'s or not; with and
    // without the conditional `D`.
    for name in ["VarY", "VarU"] {
        for discharge in [false, true] {
            let mut definition = Definition::new(&["A"])
                .constructor("n", &["A"], "A")
                .constructor("k", &["A"], "A")
                .constructor("j", &["A", "A"], "A")
                .constructor("m", &["Int"], "A")
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .head("q", &["A", "A", "A"], "Int")
                .head("f", &["A", "A"], "S")
                .equation(
                    app(
                        "q",
                        vec![
                            cons("c"),
                            app("n", vec![app("n", vec![cons("c")])]),
                            cons("d"),
                        ],
                    ),
                    int(0),
                )
                .equation(
                    app(
                        "f",
                        vec![var("VarV", "A"), app("k", vec![var("VarY", "A")])],
                    ),
                    app(
                        "f",
                        vec![
                            var("VarV", "A"),
                            app("j", vec![var("VarV", "A"), var("VarY", "A")]),
                        ],
                    ),
                )
                .equation(
                    app(
                        "f",
                        vec![
                            app("n", vec![var("VarY", "A")]),
                            app("k", vec![var("VarW", "A")]),
                        ],
                    ),
                    undefined(),
                )
                .equation(
                    app(
                        "f",
                        vec![
                            app("n", vec![app("n", vec![var(name, "A")])]),
                            app("j", vec![var("VarW", "A"), var("VarY2", "A")]),
                        ],
                    ),
                    app(
                        "f",
                        vec![
                            app(
                                "m",
                                vec![app(
                                    "q",
                                    vec![var(name, "A"), var("VarW", "A"), var("VarY2", "A")],
                                )],
                            ),
                            cons("c"),
                        ],
                    ),
                );
            if discharge {
                definition = definition.conditional(
                    app("f", vec![app("m", vec![int_var("VarX")]), cons("c")]),
                    app("mk", vec![div(int_var("VarX"), int(0))]),
                    requires_eq("VarX", 3),
                );
            }
            probes.push(probe(
                &format!("review 5 F1 ({name}, discharge {discharge})"),
                definition,
                vec![app(
                    "f",
                    vec![
                        app("n", vec![app("n", vec![cons("c")])]),
                        app("k", vec![cons("d")]),
                    ],
                )],
                vec![app("f", vec![app("m", vec![int(0)]), cons("c")])],
            ));
        }
    }
    // Review 5, F2: the bound fallback; `count` pairs of constructors, with and without `D`.
    for count in [3, 70] {
        for discharge in [false, true] {
            let mut definition = Definition::new(&["A"])
                .constructor("m", &["Int"], "A")
                .constructor("c1", &[], "A")
                .constructor("c2", &[], "A");
            for index in 0..count {
                definition = definition
                    .constructor(&format!("n{index}"), &["A"], "A")
                    .constructor(&format!("s{index}"), &["A"], "A");
            }
            definition = definition
                .head("v", &["A"], "A")
                .head("p", &["A", "A"], "A")
                .head("r", &["A", "A"], "Int")
                .head("f", &["A"], "S");
            for index in 0..count {
                definition = definition.equation(
                    app("v", vec![app(&format!("n{index}"), vec![var("VarZ", "A")])]),
                    app(&format!("s{index}"), vec![var("VarZ", "A")]),
                );
            }
            definition = definition
                .equation(
                    app(
                        "p",
                        vec![
                            app("s0", vec![var("VarA", "A")]),
                            app("s0", vec![var("VarB", "A")]),
                        ],
                    ),
                    app(
                        "m",
                        vec![app("r", vec![var("VarA", "A"), var("VarB", "A")])],
                    ),
                )
                .equation(app("r", vec![cons("c1"), cons("c2")]), int(0))
                .equation(
                    app(
                        "f",
                        vec![app(
                            "p",
                            vec![
                                app("v", vec![var("VarW1", "A")]),
                                app("v", vec![var("VarW2", "A")]),
                            ],
                        )],
                    ),
                    undefined(),
                );
            if discharge {
                definition = definition.conditional(
                    app("f", vec![app("m", vec![int_var("VarX")])]),
                    app("mk", vec![div(int_var("VarX"), int(0))]),
                    requires_eq("VarX", 3),
                );
            }
            probes.push(probe(
                &format!("review 5 F2 (count {count}, discharge {discharge})"),
                definition,
                vec![app(
                    "f",
                    vec![app(
                        "p",
                        vec![
                            app("v", vec![app("n0", vec![cons("c1")])]),
                            app("v", vec![app("n0", vec![cons("c2")])]),
                        ],
                    )],
                )],
                vec![app("f", vec![app("m", vec![int(0)])])],
            ));
        }
    }
    // Round 7, from the random run with total heads (seed 0x5eed0006, case 2466, minimized):
    // `e(f(X)) = m(1 /Int 0)` with `e` total makes `f(c)` undefined, which the scan of `f(c)`
    // does not see (no `f` equation, no peak); the documented assumption, excused.
    probes.push(Probe {
        excused: true,
        ..probe(
            "round 7 total head of another equation",
            Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("m", &["Int"], "A")
                .total_head("e", &["A"], "A")
                .head("f", &["A"], "A")
                .equation(
                    app("e", vec![app("f", vec![var("VarX", "A")])]),
                    app("m", vec![div(int(1), int(0))]),
                ),
            vec![],
            vec![app("f", vec![cons("c")])],
        )
    });
    // Round 7, from the random run with total heads (seed 0x5eed0006, case 16195, minimized):
    // the peak of `g(X, 3) = f(c)` and `g(k(d), 3) = m(2 /Int 0)` at `g(k(d), 3)` makes `f(c)`
    // undefined. The equation `g(g(f(c), 0), 1) = k(g(g(d, 2), 0))` binds its first argument by
    // membership in `g(f(c), 0)`, which is then undefined, so it states nothing, and some model
    // defines `g(g(d, 2), 0)`. Round 7 read the ground equation as an equality between its
    // sides and excused the backend's claims on `g(g(d, 2), 0)`; the oracle must not prove it
    // undefined.
    // `f(c)` itself is undefined through the peak of two `g` equations whose side holds `f`:
    // the documented cross-head assumption, excused.
    probes.push(Probe {
        free: vec![app("g", vec![app("g", vec![cons("d"), int(2)]), int(0)])],
        excused: true,
        ..probe(
            "round 7 vacuous left-hand side",
            Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .constructor("k", &["A"], "A")
                .constructor("m", &["Int"], "A")
                .head("f", &["A"], "A")
                .head("g", &["A", "Int"], "A")
                .equation(
                    app(
                        "g",
                        vec![app("g", vec![app("f", vec![cons("c")]), int(0)]), int(1)],
                    ),
                    app(
                        "k",
                        vec![app("g", vec![app("g", vec![cons("d"), int(2)]), int(0)])],
                    ),
                )
                .equation(
                    app("g", vec![var("VarX", "A"), int(3)]),
                    app("f", vec![cons("c")]),
                )
                .equation(
                    app("g", vec![app("k", vec![cons("d")]), int(3)]),
                    app("m", vec![div(int(2), int(0))]),
                ),
            vec![
                app("g", vec![app("k", vec![cons("d")]), int(3)]),
                app("g", vec![app("g", vec![cons("d"), int(2)]), int(0)]),
            ],
            vec![app("f", vec![cons("c")])],
        )
    });
    // Review 7, F1: `f(m(I)) = c requires I ==Int 0` is refuted at `f(m(1))`, and `e(f(m(1))) =
    // m(1 /Int 0)` with `e` total makes `f(m(1))` undefined without any peak. Its own conditional
    // equation matches `f(m(1))`, so the total-head limit does not excuse it.
    let conditional_f = Definition::new(&["A"])
        .constructor("c", &[], "A")
        .constructor("k", &["A"], "A")
        .constructor("m", &["Int"], "A")
        .total_head("e", &["A"], "A")
        .head("f", &["A"], "A")
        .head("q", &["A"], "A")
        .conditional(
            app("f", vec![app("m", vec![int_var("VarI")])]),
            cons("c"),
            requires_eq("VarI", 0),
        );
    let f_m_1 = app("f", vec![app("m", vec![int(1)])]);
    probes.push(probe(
        "review 7 F1",
        conditional_f.clone().equation(
            app("e", vec![f_m_1.clone()]),
            app("m", vec![div(int(1), int(0))]),
        ),
        vec![],
        vec![f_m_1.clone()],
    ));
    // Round 8: `q(c) = k(f(m(1)))` beside `q(c) = m(1 /Int 0)` makes `f(m(1))` undefined through
    // a peak of `q`, whose side holds `f`; the same conditional `f` equation matches `f(m(1))`,
    // so the peak assumption does not excuse it.
    probes.push(probe(
        "round 8 right-hand side of another head",
        conditional_f
            .equation(app("q", vec![cons("c")]), app("k", vec![f_m_1.clone()]))
            .equation(
                app("q", vec![cons("c")]),
                app("m", vec![div(int(1), int(0))]),
            ),
        vec![],
        vec![f_m_1],
    ));
    // Review 6, F1 and F2: `e : A -> A` a total equation head, `sz : A -> Int` a total
    // function; `g(d) = m(1 /Int 0)` beside `g(d) = C[g(t)]` with `C` built from total symbols
    // only, so `g(t)` is undefined; F1 adds `g(m(I)) = c requires I ==Int 0`, refuted at
    // `g(m(1))`.
    for (label, held, conditional) in [
        ("F1", app("g", vec![app("m", vec![int(1)])]), true),
        ("F2", app("g", vec![app("s", vec![cons("c")])]), false),
    ] {
        for (context, second) in [
            ("k(e(_))", app("k", vec![app("e", vec![held.clone()])])),
            ("e(_)", app("e", vec![held.clone()])),
            ("m(sz(_))", app("m", vec![app("sz", vec![held.clone()])])),
            ("k(_)", app("k", vec![held.clone()])),
        ] {
            let mut definition = Definition::new(&["A"])
                .constructor("c", &[], "A")
                .constructor("d", &[], "A")
                .constructor("k", &["A"], "A")
                .constructor("s", &["A"], "A")
                .constructor("m", &["Int"], "A")
                .total_head("e", &["A"], "A")
                .total_function("sz", &["A"], "Int")
                .head("g", &["A"], "A")
                .equation(
                    app("g", vec![cons("d")]),
                    app("m", vec![div(int(1), int(0))]),
                )
                .equation(app("g", vec![cons("d")]), second);
            if conditional {
                definition = definition.conditional(
                    app("g", vec![app("m", vec![int_var("VarI")])]),
                    cons("c"),
                    requires_eq("VarI", 0),
                );
            }
            probes.push(probe(
                &format!("review 6 {label} ({context})"),
                definition,
                vec![],
                vec![held.clone()],
            ));
        }
    }
    probes
}

/// `pattern` with its variables renamed by `renaming`.
fn renamed(pattern: &Pat, renaming: &BTreeMap<String, String>) -> Pat {
    match pattern {
        Pat::Var(name, sort) => Pat::Var(renaming[name].clone(), sort.clone()),
        Pat::App(name, arguments) => Pat::App(
            name.clone(),
            arguments
                .iter()
                .map(|argument| renamed(argument, renaming))
                .collect(),
        ),
        Pat::Int(value) => Pat::Int(*value),
        Pat::Inj(from, to, inner) => {
            Pat::Inj(from.clone(), to.clone(), Box::new(renamed(inner, renaming)))
        }
        Pat::Div(left, right) => Pat::Div(
            Box::new(renamed(left, renaming)),
            Box::new(renamed(right, renaming)),
        ),
    }
}

/// The variable names [`variant`] draws from: few, so that equations often share them.
const VARIANT_NAMES: [&str; 5] = ["VarX", "VarY", "VarZ", "VarU", "VarW"];

/// A definition with the axioms of `definition`, written differently: each equation's variables
/// renamed one-to-one to names drawn from [`VARIANT_NAMES`] (so that independent variables of
/// different equations often share a name, and a name an equation keeps for one variable
/// another uses for an unrelated one), and the equations in another order. Each equation
/// quantifies its variables on its own, so this denotes the same theory, and every claim the
/// backend makes must be the same.
fn variant(definition: &Definition, rng: &mut Rng) -> Definition {
    let mut variant = definition.clone();
    for equation in &mut variant.equations {
        let mut variables = BTreeMap::new();
        pattern_variables(&equation.lhs, &mut variables);
        pattern_variables(&equation.rhs, &mut variables);
        if variables.len() > VARIANT_NAMES.len() {
            continue;
        }
        let mut names = VARIANT_NAMES.to_vec();
        let renaming = variables
            .keys()
            .map(|name| {
                let chosen = names.remove(rng.below(names.len()));
                (name.clone(), chosen.to_string())
            })
            .collect::<BTreeMap<_, _>>();
        equation.lhs = renamed(&equation.lhs, &renaming);
        equation.rhs = renamed(&equation.rhs, &renaming);
        if let Some(requires) = &mut equation.requires {
            requires.variable.clone_from(&renaming[&requires.variable]);
        }
    }
    for index in (1..variant.equations.len()).rev() {
        variant.equations.swap(index, rng.below(index + 1));
    }
    variant
}

/// Variants of every reviewer probe ([`variant`]): the backend claims nothing the oracle
/// refutes for any way of writing the same axioms. `KRUST_DEFINEDNESS_ORACLE_VARIANTS`
/// (default 2) variants per probe.
#[test]
fn variants_of_the_reviewers_probes_claim_no_definedness_the_axioms_refute() {
    on_large_stack(|| {
        let variants = environment("KRUST_DEFINEDNESS_ORACLE_VARIANTS", 2);
        let seed = environment("KRUST_DEFINEDNESS_ORACLE_SEED", DEFAULT_SEED);
        let mut total = Tally::default();
        for (index, probe) in probes().into_iter().enumerate() {
            for number in 0..variants {
                let mut rng = Rng(seed
                    ^ u64::try_from(index)
                        .unwrap()
                        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    ^ number.wrapping_mul(0xbf58_476d_1ce4_e5b9));
                let definition = variant(&probe.definition, &mut rng);
                let (_, tally) = check_definition(
                    &format!("{} (variant {number})", probe.name),
                    &definition,
                    &probe.seeds,
                    &probe.undefined,
                    &mut rng,
                );
                total.add(tally);
            }
            if total.failures.len() >= 20 {
                break;
            }
        }
        eprintln!(
            "definedness oracle, probe variants: {} definitions ({} inconsistent), {} terms explored, {} undefined terms checked ({} also by \\ceil), {} excused, {} failures",
            total.definitions,
            total.inconsistent,
            total.universe,
            total.checked,
            total.evaluated,
            total.excused,
            total.failures.len()
        );
        assert!(total.failures.is_empty(), "{}", total.failures.join("\n"));
    });
}

/// Every reviewer probe: the oracle proves its query undefined, and the backend claims
/// nothing the oracle refutes, under the default and the minimal bounds.
#[test]
fn the_reviewers_probes_claim_no_definedness_the_axioms_refute() {
    on_large_stack(|| {
        let mut total = Tally::default();
        let mut uncovered = Vec::new();
        for probe in probes() {
            let mut rng = Rng(DEFAULT_SEED);
            let (verdicts, tally) = check_definition(
                &probe.name,
                &probe.definition,
                &probe.seeds,
                &probe.undefined,
                &mut rng,
            );
            assert!(!verdicts.inconsistent, "{} is inconsistent", probe.name);
            for term in &probe.free {
                let term = pattern_kore(term);
                if verdicts.undefined.contains(&term) {
                    uncovered.push(format!("{}: {term} proven undefined", probe.name));
                }
            }
            for query in &probe.undefined {
                let term = pattern_kore(query);
                if !verdicts.undefined.contains(&term) {
                    uncovered.push(format!("{}: {term} not proven undefined", probe.name));
                }
                let checked = verdicts.queries.iter().find(|checked| checked.term == term);
                if checked.is_some_and(|checked| !checked.terminates) {
                    uncovered.push(format!("{}: {term} not shown to terminate", probe.name));
                }
                let excused = checked.is_some_and(|checked| checked.excused);
                if excused != probe.excused {
                    uncovered.push(format!(
                        "{}: {term} excused {excused}, expected {}",
                        probe.name, probe.excused
                    ));
                }
            }
            total.add(tally);
        }
        eprintln!(
            "definedness oracle, probes: {} definitions, {} terms explored, {} undefined terms checked ({} also by \\ceil), {} excused, {} failures",
            total.definitions,
            total.universe,
            total.checked,
            total.evaluated,
            total.excused,
            total.failures.len()
        );
        assert!(uncovered.is_empty(), "{}", uncovered.join("\n"));
        assert!(total.failures.is_empty(), "{}", total.failures.join("\n"));
    });
}
