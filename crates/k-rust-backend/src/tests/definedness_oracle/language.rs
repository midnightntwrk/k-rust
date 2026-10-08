//! The oracle's definition language: patterns, symbols, equations, and their KORE text.

use std::{collections::BTreeMap, fmt::Write as _};

/// A pattern of the oracle's language. Sorts and symbols are named as in the KORE the definition
/// is written to (without the `Sort` prefix for sorts).
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(super) enum Pat {
    /// A variable: name, sort.
    Var(String, String),
    App(String, Vec<Pat>),
    Int(i64),
    /// `inj{from, to}(pattern)`.
    Inj(String, String, Box<Pat>),
    /// `\and(pattern, X:S)`: an alias of the pattern's instance (left-hand sides only).
    As(Box<Pat>, String, String),
    /// A list of `Int` elements: the elements before the rest variable, the rest variable (of
    /// sort `List`) if any, and the elements after it.
    List(Vec<Pat>, Option<String>, Vec<Pat>),
}

pub(super) fn var(name: &str, sort: &str) -> Pat {
    Pat::Var(name.into(), sort.into())
}

pub(super) fn int_var(name: &str) -> Pat {
    var(name, "Int")
}

pub(super) fn app(name: &str, arguments: Vec<Pat>) -> Pat {
    Pat::App(name.into(), arguments)
}

pub(super) fn cons(name: &str) -> Pat {
    app(name, Vec::new())
}

pub(super) fn int(value: i64) -> Pat {
    Pat::Int(value)
}

pub(super) fn inj(from: &str, to: &str, pattern: Pat) -> Pat {
    Pat::Inj(from.into(), to.into(), Box::new(pattern))
}

/// The list pattern `prefix rest suffix`.
pub(super) fn list(prefix: Vec<Pat>, rest: Option<&str>, suffix: Vec<Pat>) -> Pat {
    Pat::List(prefix, rest.map(Into::into), suffix)
}

/// `left /Int right` (`INT.tdiv`, partial: undefined where `right` is zero).
pub(super) fn div(left: Pat, right: Pat) -> Pat {
    app("divInt", vec![left, right])
}

/// `mk(1 /Int 0)`: undefined.
pub(super) fn undefined() -> Pat {
    app("mk", vec![div(int(1), int(0))])
}

/// `left ==Int right` as a condition.
pub(super) fn int_equals(left: Pat, right: Pat) -> Pat {
    app("eqInt", vec![left, right])
}

/// `variable ==Int value` as a `requires`.
pub(super) fn requires_eq(variable: &str, value: i64) -> Option<Pat> {
    Some(int_equals(int_var(variable), int(value)))
}

/// How a symbol is declared.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Kind {
    /// `constructor, functional, injective`.
    Constructor,
    /// `anywhere` (an equation head); `value-production` when `value_production`, `total` when
    /// `total`.
    Head { value_production: bool, total: bool },
    /// `function`, `total` when `total`.
    Function { total: bool },
    /// A hooked `Int` or `Bool` operation of the prelude.
    Hook,
}

#[derive(Clone, Debug)]
pub(super) struct Symbol {
    pub(super) name: String,
    pub(super) arguments: Vec<String>,
    pub(super) result: String,
    pub(super) kind: Kind,
}

impl Symbol {
    /// Whether the symbol is defined on defined arguments: a constructor, or declared total.
    pub(super) fn total(&self) -> bool {
        match self.kind {
            Kind::Constructor => true,
            Kind::Head { total, .. } | Kind::Function { total } => total,
            Kind::Hook => self.name != "divInt",
        }
    }

    pub(super) fn is_head(&self) -> bool {
        matches!(self.kind, Kind::Head { .. })
    }

    pub(super) fn is_function(&self) -> bool {
        matches!(self.kind, Kind::Function { .. } | Kind::Hook)
    }
}

/// The priority of an equation: lower applies first. `owise` is 200, the default 50.
pub(super) const DEFAULT_PRIORITY: u8 = 50;
pub(super) const OWISE_PRIORITY: u8 = 200;

#[derive(Clone, Debug)]
pub(super) struct Equation {
    pub(super) lhs: Pat,
    pub(super) rhs: Pat,
    /// A Boolean term the equation requires true.
    pub(super) requires: Option<Pat>,
    /// A Boolean term the equation ensures true: where it is false the instance is `\bottom`.
    pub(super) ensures: Option<Pat>,
    pub(super) priority: u8,
    /// `Some((greater, lesser))` for an overload equation.
    pub(super) overload: Option<(String, String)>,
    /// `symbolic`: an axiom the evaluator never applies to a ground term (precondition P4).
    pub(super) symbolic: bool,
}

impl Equation {
    pub(super) fn root(&self) -> &str {
        match &self.lhs {
            Pat::App(name, _) => name,
            _ => panic!("a left-hand side is an application"),
        }
    }
}

/// A definition over the hooked `Int` and `Bool`: sorts, subsorts (the order is the closure of
/// the pairs given), symbols, equations and overloads. `mk : Int -> S` is always declared.
#[derive(Clone, Debug, Default)]
pub(super) struct Definition {
    pub(super) sorts: Vec<String>,
    pub(super) subsorts: Vec<(String, String)>,
    pub(super) symbols: Vec<Symbol>,
    pub(super) equations: Vec<Equation>,
    /// Whether the hooked sort `List` of `Int` elements is declared.
    pub(super) lists: bool,
}

/// The prelude's hooked operations: `divInt` (`INT.tdiv`), `addInt`, `eqInt`, `ltInt`,
/// `notBool`.
pub(super) const HOOKS: [(&str, &[&str], &str, &str); 5] = [
    ("divInt", &["Int", "Int"], "Int", "INT.tdiv"),
    ("addInt", &["Int", "Int"], "Int", "INT.add"),
    ("eqInt", &["Int", "Int"], "Bool", "INT.eq"),
    ("ltInt", &["Int", "Int"], "Bool", "INT.lt"),
    ("notBool", &["Bool"], "Bool", "BOOL.not"),
];

impl Definition {
    pub(super) fn new(sorts: &[&str]) -> Self {
        let mut definition = Self::default();
        definition.sorts.push("S".into());
        for sort in sorts {
            if *sort != "S" {
                definition.sorts.push((*sort).into());
            }
        }
        if sorts.contains(&"A") {
            definition.symbols.push(Symbol {
                name: "eqA".into(),
                arguments: vec!["A".into(), "A".into()],
                result: "Bool".into(),
                kind: Kind::Hook,
            });
        }
        for (name, arguments, result, _) in HOOKS {
            definition.symbols.push(Symbol {
                name: name.into(),
                arguments: arguments.iter().map(|sort| (*sort).into()).collect(),
                result: result.into(),
                kind: Kind::Hook,
            });
        }
        definition.constructor("mk", &["Int"], "S")
    }

    /// Declares the hooked sort `List` of `Int` elements.
    pub(super) fn with_lists(mut self) -> Self {
        self.lists = true;
        self
    }

    pub(super) fn symbol(
        mut self,
        name: &str,
        arguments: &[&str],
        result: &str,
        kind: Kind,
    ) -> Self {
        self.symbols.push(Symbol {
            name: name.into(),
            arguments: arguments.iter().map(|sort| (*sort).into()).collect(),
            result: result.into(),
            kind,
        });
        self
    }

    pub(super) fn constructor(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, Kind::Constructor)
    }

    /// A value production: an equation head whose irreducible applications are values.
    pub(super) fn head(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(
            name,
            arguments,
            result,
            Kind::Head {
                value_production: true,
                total: false,
            },
        )
    }

    /// An equation head declared `total`.
    pub(super) fn total_head(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(
            name,
            arguments,
            result,
            Kind::Head {
                value_production: false,
                total: true,
            },
        )
    }

    pub(super) fn function(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, Kind::Function { total: false })
    }

    /// A function declared `total`.
    pub(super) fn total_function(self, name: &str, arguments: &[&str], result: &str) -> Self {
        self.symbol(name, arguments, result, Kind::Function { total: true })
    }

    /// `sub < sup`.
    pub(super) fn subsort(mut self, sub: &str, sup: &str) -> Self {
        self.subsorts.push((sub.into(), sup.into()));
        self
    }

    pub(super) fn equation(self, lhs: Pat, rhs: Pat) -> Self {
        self.conditional(lhs, rhs, None)
    }

    pub(super) fn conditional(self, lhs: Pat, rhs: Pat, requires: Option<Pat>) -> Self {
        self.full(lhs, rhs, requires, None, DEFAULT_PRIORITY)
    }

    pub(super) fn full(
        mut self,
        lhs: Pat,
        rhs: Pat,
        requires: Option<Pat>,
        ensures: Option<Pat>,
        priority: u8,
    ) -> Self {
        self.equations.push(Equation {
            lhs,
            rhs,
            requires,
            ensures,
            priority,
            overload: None,
            symbolic: false,
        });
        self
    }

    /// Marks the last equation `symbolic`.
    pub(super) fn symbolic(mut self) -> Self {
        self.equations
            .last_mut()
            .expect("an equation to mark")
            .symbolic = true;
        self
    }

    /// The overload equation of `greater` over `lesser`:
    /// `greater(inj(X1), ..., inj(Xn)) = inj(lesser(X1, ..., Xn))`, an injection omitted where
    /// the two sorts are equal.
    pub(super) fn overload(mut self, greater: &str, lesser: &str) -> Self {
        let (greater_symbol, lesser_symbol) = (
            self.symbol_named(greater).clone(),
            self.symbol_named(lesser).clone(),
        );
        let variables = lesser_symbol
            .arguments
            .iter()
            .enumerate()
            .map(|(index, sort)| var(&format!("K{index}"), sort))
            .collect::<Vec<_>>();
        let lhs = app(
            greater,
            variables
                .iter()
                .zip(&greater_symbol.arguments)
                .zip(&lesser_symbol.arguments)
                .map(|((variable, big), small)| {
                    if big == small {
                        variable.clone()
                    } else {
                        inj(small, big, variable.clone())
                    }
                })
                .collect(),
        );
        let lowered = app(lesser, variables);
        let rhs = if greater_symbol.result == lesser_symbol.result {
            lowered
        } else {
            inj(&lesser_symbol.result, &greater_symbol.result, lowered)
        };
        self.equations.push(Equation {
            lhs,
            rhs,
            requires: None,
            ensures: None,
            priority: DEFAULT_PRIORITY,
            overload: Some((greater.into(), lesser.into())),
            symbolic: false,
        });
        self
    }

    pub(super) fn symbol_named(&self, name: &str) -> &Symbol {
        self.symbols
            .iter()
            .find(|symbol| symbol.name == name)
            .unwrap_or_else(|| panic!("undeclared symbol {name}"))
    }

    /// The pairs `(greater, lesser)` of the overload equations, transitively closed.
    pub(super) fn overloads(&self) -> Vec<(String, String)> {
        let mut pairs = self
            .equations
            .iter()
            .filter_map(|equation| equation.overload.clone())
            .collect::<Vec<_>>();
        loop {
            let mut added = Vec::new();
            for (greater, middle) in &pairs {
                for (other, lesser) in &pairs {
                    if other == middle && !pairs.contains(&(greater.clone(), lesser.clone())) {
                        added.push((greater.clone(), lesser.clone()));
                    }
                }
            }
            if added.is_empty() {
                return pairs;
            }
            pairs.extend(added);
            pairs.sort();
            pairs.dedup();
        }
    }

    /// The reflexive-transitive closure of the subsort pairs, over the declared sorts and
    /// `Int`, `Bool`.
    pub(super) fn sort_order(&self) -> BTreeMap<String, Vec<String>> {
        let mut sorts = self.sorts.clone();
        sorts.push("Int".into());
        sorts.push("Bool".into());
        if self.lists {
            sorts.push("List".into());
        }
        let mut below = sorts
            .iter()
            .map(|sort| (sort.clone(), vec![sort.clone()]))
            .collect::<BTreeMap<_, _>>();
        loop {
            let mut changed = false;
            for (sub, sup) in &self.subsorts {
                let under = below[sub].clone();
                let entry = below.get_mut(sup).expect("a declared sort");
                for sort in under {
                    if !entry.contains(&sort) {
                        entry.push(sort);
                        changed = true;
                    }
                }
            }
            if !changed {
                return below;
            }
        }
    }

    /// The KORE text of the definition, each equation labelled `eq{index}`.
    pub(super) fn kore(&self) -> String {
        let mut source = String::from(
            "[]\nmodule MAIN\nhooked-sort SortInt{} [hook{}(\"INT.Int\"), hasDomainValues{}()]\nhooked-sort SortBool{} [hook{}(\"BOOL.Bool\"), hasDomainValues{}()]\n",
        );
        for (name, arguments, result, hook) in HOOKS {
            let total = if name == "divInt" { "" } else { "total{}(), " };
            writeln!(
                source,
                "hooked-symbol {name}{{}}({}) : {} [function{{}}(), {total}hook{{}}(\"{hook}\")]",
                arguments
                    .iter()
                    .map(|sort| sort_kore(sort))
                    .collect::<Vec<_>>()
                    .join(", "),
                sort_kore(result)
            )
            .unwrap();
        }
        if self.lists {
            source.push_str(concat!(
                "hooked-sort SortList{} [hook{}(\"LIST.List\"), unit{}(listUnit{}()), element{}(listItem{}()), concat{}(listConcat{}())]\n",
                "hooked-symbol listUnit{}() : SortList{} [function{}(), functional{}(), total{}(), hook{}(\"LIST.unit\")]\n",
                "hooked-symbol listItem{}(SortInt{}) : SortList{} [function{}(), functional{}(), total{}(), hook{}(\"LIST.element\")]\n",
                "hooked-symbol listConcat{}(SortList{}, SortList{}) : SortList{} [function{}(), functional{}(), total{}(), hook{}(\"LIST.concat\"), assoc{}(), unit{}(listUnit{}())]\n",
            ));
        }
        for sort in &self.sorts {
            writeln!(source, "sort Sort{sort}{{}} []").unwrap();
        }
        if !self.subsorts.is_empty() {
            source.push_str("symbol inj{From, To}(From) : To [sortInjection{}()]\n");
        }
        for (sup, below) in self.sort_order() {
            for sub in below.iter().filter(|sub| **sub != sup) {
                let (sub, sup) = (sort_kore(sub), sort_kore(&sup));
                writeln!(
                    source,
                    r"axiom{{R}} \exists{{R}}(Value:{sup}, \equals{{{sup}, R}}(Value:{sup}, inj{{{sub}, {sup}}}(From:{sub}))) [subsort{{{sub}, {sup}}}()]"
                )
                .unwrap();
            }
        }
        if self.sorts.iter().any(|sort| sort == "A") {
            source.push_str(
                "hooked-symbol eqA{}(SortA{}, SortA{}) : SortBool{} [function{}(), total{}(), hook{}(\"KEQUAL.eq\")]\n",
            );
        }
        for symbol in self
            .symbols
            .iter()
            .filter(|symbol| symbol.kind != Kind::Hook)
        {
            let attributes = match symbol.kind {
                Kind::Constructor => "constructor{}(), functional{}(), injective{}()".to_owned(),
                Kind::Head {
                    value_production,
                    total,
                } => {
                    let mut attributes = "anywhere{}()".to_owned();
                    if total {
                        attributes.push_str(", total{}()");
                    }
                    if value_production {
                        attributes.push_str(", value-production{}()");
                    }
                    attributes
                }
                Kind::Function { total } => {
                    if total {
                        "function{}(), total{}()".to_owned()
                    } else {
                        "function{}()".to_owned()
                    }
                }
                Kind::Hook => unreachable!("hooks are in the prelude"),
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
        for (index, equation) in self.equations.iter().enumerate() {
            source.push_str(&self.equation_kore(index, equation));
            source.push('\n');
        }
        source.push_str("endmodule []\n");
        source
    }

    fn equation_kore(&self, index: usize, equation: &Equation) -> String {
        let Pat::App(head, arguments) = &equation.lhs else {
            panic!("a left-hand side is a head application")
        };
        let symbol = self.symbol_named(head);
        let result = sort_kore(&symbol.result);
        if let Some((greater, lesser)) = &equation.overload {
            return format!(
                r"axiom{{R}} \equals{{{result}, R}}({}, {}) [symbol-overload{{}}({greater}{{}}(), {lesser}{{}}()), label{{}}({})]",
                pattern_kore(&equation.lhs),
                pattern_kore(&equation.rhs),
                quoted_label(index)
            );
        }
        let memberships = arguments
            .iter()
            .zip(&symbol.arguments)
            .enumerate()
            .rev()
            .fold(
                r"\top{R}()".to_string(),
                |rest, (position, (argument, sort))| {
                    let sort = sort_kore(sort);
                    format!(
                        r"\and{{R}}(\in{{{sort}, R}}(X{position}:{sort}, {}), {rest})",
                        pattern_kore(argument)
                    )
                },
            );
        let requires = match &equation.requires {
            None => r"\top{R}()".to_string(),
            Some(requires) => format!(
                r#"\equals{{SortBool{{}}, R}}({}, \dv{{SortBool{{}}}}("true"))"#,
                pattern_kore(requires)
            ),
        };
        let ensures = match &equation.ensures {
            None => format!(r"\top{{{result}}}()"),
            Some(ensures) => format!(
                r#"\equals{{SortBool{{}}, {result}}}({}, \dv{{SortBool{{}}}}("true"))"#,
                pattern_kore(ensures)
            ),
        };
        let parameters = symbol
            .arguments
            .iter()
            .enumerate()
            .map(|(position, sort)| format!("X{position}:{}", sort_kore(sort)))
            .collect::<Vec<_>>()
            .join(", ");
        let mut attributes = format!("label{{}}({})", quoted_label(index));
        if symbol.is_head() {
            attributes.push_str(", anywhere{}()");
        }
        if equation.symbolic {
            attributes.push_str(", symbolic{}()");
        }
        if equation.priority == OWISE_PRIORITY {
            attributes.push_str(", owise{}()");
        } else if equation.priority != DEFAULT_PRIORITY {
            write!(attributes, ", priority{{}}(\"{}\")", equation.priority).unwrap();
        }
        format!(
            r"axiom{{R}} \implies{{R}}(\and{{R}}({requires}, {memberships}), \equals{{{result}, R}}({head}{{}}({parameters}), \and{{{result}}}({}, {ensures}))) [{attributes}]",
            pattern_kore(&equation.rhs)
        )
    }
}

/// The label of equation `index` (`eq{index}`), quoted for KORE.
fn quoted_label(index: usize) -> String {
    format!("\"eq{index}\"")
}

/// The index of the equation a backend rule was internalized from, by its label.
pub(super) fn equation_index(label: Option<&str>) -> Option<usize> {
    label?.strip_prefix("eq")?.parse().ok()
}

pub(super) fn sort_kore(sort: &str) -> String {
    format!("Sort{sort}{{}}")
}

pub(super) fn pattern_kore(pattern: &Pat) -> String {
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
        Pat::As(pattern, name, sort) => format!(
            r"\and{{{0}}}({1}, {name}:{0})",
            sort_kore(sort),
            pattern_kore(pattern)
        ),
        Pat::List(prefix, rest, suffix) => {
            let mut parts = prefix
                .iter()
                .map(|element| format!("listItem{{}}({})", pattern_kore(element)))
                .collect::<Vec<_>>();
            if let Some(rest) = rest {
                parts.push(format!("{rest}:SortList{{}}"));
            }
            parts.extend(
                suffix
                    .iter()
                    .map(|element| format!("listItem{{}}({})", pattern_kore(element))),
            );
            list_kore(parts)
        }
    }
}

/// The concatenation of `parts` (each a `List` pattern), right-nested; the unit when empty.
pub(super) fn list_kore(mut parts: Vec<String>) -> String {
    let Some(mut list) = parts.pop() else {
        return "listUnit{}()".to_owned();
    };
    while let Some(part) = parts.pop() {
        list = format!("listConcat{{}}({part}, {list})");
    }
    list
}

/// The variables of `pattern` with their sorts.
pub(super) fn pattern_variables(pattern: &Pat, into: &mut BTreeMap<String, String>) {
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
        Pat::As(pattern, name, sort) => {
            pattern_variables(pattern, into);
            into.insert(name.clone(), sort.clone());
        }
        Pat::List(prefix, rest, suffix) => {
            for element in prefix.iter().chain(suffix) {
                pattern_variables(element, into);
            }
            if let Some(rest) = rest {
                into.insert(rest.clone(), "List".into());
            }
        }
    }
}

/// `pattern` with its variables renamed by `renaming` (unlisted ones kept).
pub(super) fn renamed(pattern: &Pat, renaming: &BTreeMap<String, String>) -> Pat {
    let name = |name: &String| renaming.get(name).cloned().unwrap_or_else(|| name.clone());
    match pattern {
        Pat::Var(variable, sort) => Pat::Var(name(variable), sort.clone()),
        Pat::App(symbol, arguments) => Pat::App(
            symbol.clone(),
            arguments
                .iter()
                .map(|argument| renamed(argument, renaming))
                .collect(),
        ),
        Pat::Int(value) => Pat::Int(*value),
        Pat::Inj(from, to, inner) => {
            Pat::Inj(from.clone(), to.clone(), Box::new(renamed(inner, renaming)))
        }
        Pat::As(inner, variable, sort) => Pat::As(
            Box::new(renamed(inner, renaming)),
            name(variable),
            sort.clone(),
        ),
        Pat::List(prefix, rest, suffix) => Pat::List(
            prefix
                .iter()
                .map(|element| renamed(element, renaming))
                .collect(),
            rest.as_ref().map(name),
            suffix
                .iter()
                .map(|element| renamed(element, renaming))
                .collect(),
        ),
    }
}
