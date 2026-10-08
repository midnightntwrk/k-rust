//! The printer's term model: the KORE term model of the LLVM backend's `kprint`.
//!
//! `kprint` represents every pattern except variables and string literals as a composite pattern
//! whose constructor is a symbol: the matching-logic connectives become the builtin symbols
//! `\and`, `\equals`, `\dv`, ... with their sort parameters as formal arguments. Every algorithm
//! of this crate is a port of an algorithm over that model, so the model is reproduced here.

use std::collections::BTreeMap;

use k_rust::kore::ast::{Associativity, Pattern, Sort, Symbol, Variable, VariableKind};

/// A symbol occurrence: its name, its sort parameters, and, once instantiated, its argument and result sorts.
#[derive(Clone, Debug)]
pub(crate) struct Sym {
    pub name: String,
    pub formals: Vec<Sort>,
    pub arguments: Vec<Sort>,
    pub sort: Option<Sort>,
}

impl Sym {
    pub fn new(name: impl Into<String>, formals: Vec<Sort>) -> Self {
        Self {
            name: name.into(),
            formals,
            arguments: Vec::new(),
            sort: None,
        }
    }

    /// `kore_symbol::is_builtin`.
    pub fn is_builtin(&self) -> bool {
        BUILTINS.contains(&self.name.as_str())
    }
}

/// `kore_symbol::operator==`: the name and the instantiated argument sorts; sort parameters are not compared.
impl PartialEq for Sym {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.arguments == other.arguments
    }
}

/// The matching-logic symbols `kprint` never instantiates from a declaration.
pub(crate) const BUILTINS: &[&str] = &[
    "\\and",
    "\\not",
    "\\or",
    "\\implies",
    "\\iff",
    "\\forall",
    "\\exists",
    "\\ceil",
    "\\floor",
    "\\equals",
    "\\in",
    "\\top",
    "\\bottom",
    "\\dv",
    "\\rewrites",
    "\\next",
    "\\mu",
    "\\nu",
    "weakAlwaysFinally",
    "weakExistsFinally",
    "allPathGlobally",
];

/// One application: a constructor symbol and its arguments.
#[derive(Clone, Debug)]
pub(crate) struct App {
    pub sym: Sym,
    pub args: Vec<Node>,
}

/// A pattern of the printer's term model.
#[derive(Clone, Debug)]
pub(crate) enum Node {
    /// A variable, with its KORE name (`VarX`, `@VarX`) and sort.
    Var { name: String, set: bool, sort: Sort },
    /// A string literal: the argument of `\dv`.
    Str(Vec<u8>),
    /// An application of a symbol or a matching-logic connective.
    App(App),
}

impl Node {
    pub fn app(sym: Sym, args: Vec<Self>) -> Self {
        Self::App(App { sym, args })
    }

    pub fn as_app(&self) -> Option<&App> {
        match self {
            Self::App(app) => Some(app),
            _ => None,
        }
    }

    /// `kore_pattern::get_sort`: a variable's sort, or an instantiated application's result sort.
    pub fn sort(&self) -> Option<&Sort> {
        match self {
            Self::Var { sort, .. } => Some(sort),
            Self::App(app) => app.sym.sort.as_ref(),
            Self::Str(_) => None,
        }
    }

    /// A canonical text of the node, which `kprint` compares with `ast_to_string`.
    pub fn key(&self) -> String {
        let mut text = String::new();
        self.write_key(&mut text);
        text
    }

    fn write_key(&self, text: &mut String) {
        match self {
            Self::Var { name, set, sort } => {
                if *set {
                    text.push('@');
                }
                text.push_str(name);
                text.push(':');
                text.push_str(&sort.to_string());
            }
            Self::Str(bytes) => {
                text.push('"');
                text.push_str(&String::from_utf8_lossy(bytes));
                text.push('"');
            }
            Self::App(app) => {
                text.push_str(&app.sym.name);
                text.push('{');
                for (index, sort) in app.sym.formals.iter().enumerate() {
                    if index > 0 {
                        text.push(',');
                    }
                    text.push_str(&sort.to_string());
                }
                text.push_str("}(");
                for (index, argument) in app.args.iter().enumerate() {
                    if index > 0 {
                        text.push(',');
                    }
                    argument.write_key(text);
                }
                text.push(')');
            }
        }
    }
}

fn connective(name: &str, formals: Vec<Sort>, args: Vec<Node>) -> Node {
    Node::app(Sym::new(name, formals), args)
}

fn variable(variable: &Variable) -> Node {
    Node::Var {
        name: variable.name.clone(),
        set: variable.kind == VariableKind::Set,
        sort: variable.sort.clone(),
    }
}

/// Convert a KORE pattern, desugaring `\left-assoc` and `\right-assoc` applications as the LLVM KORE parser does.
#[expect(
    clippy::too_many_lines,
    reason = "one arm per KORE pattern kind, mirroring the model's connective list"
)]
pub(crate) fn from_pattern(pattern: &Pattern) -> Node {
    let many = |patterns: &[Pattern]| patterns.iter().map(from_pattern).collect::<Vec<_>>();
    let one = |pattern: &Pattern| from_pattern(pattern);
    match pattern {
        Pattern::String(value) => Node::Str(value.as_bytes().to_vec()),
        Pattern::Variable(value) => variable(value),
        Pattern::Application { symbol, arguments } => Node::app(
            Sym::new(symbol.name.clone(), symbol.sort_parameters.clone()),
            many(arguments),
        ),
        Pattern::Top { sort } => connective("\\top", vec![sort.clone()], Vec::new()),
        Pattern::Bottom { sort } => connective("\\bottom", vec![sort.clone()], Vec::new()),
        Pattern::And { sort, arguments } => {
            connective("\\and", vec![sort.clone()], many(arguments))
        }
        Pattern::Or { sort, arguments } => connective("\\or", vec![sort.clone()], many(arguments)),
        Pattern::Not { sort, argument } => {
            connective("\\not", vec![sort.clone()], vec![one(argument)])
        }
        Pattern::Next { sort, argument } => {
            connective("\\next", vec![sort.clone()], vec![one(argument)])
        }
        Pattern::Implies { sort, left, right } => {
            connective("\\implies", vec![sort.clone()], vec![one(left), one(right)])
        }
        Pattern::Iff { sort, left, right } => {
            connective("\\iff", vec![sort.clone()], vec![one(left), one(right)])
        }
        Pattern::Rewrites { sort, left, right } => connective(
            "\\rewrites",
            vec![sort.clone()],
            vec![one(left), one(right)],
        ),
        Pattern::Exists {
            sort,
            variable: bound,
            body,
        } => connective(
            "\\exists",
            vec![sort.clone()],
            vec![variable(bound), one(body)],
        ),
        Pattern::Forall {
            sort,
            variable: bound,
            body,
        } => connective(
            "\\forall",
            vec![sort.clone()],
            vec![variable(bound), one(body)],
        ),
        Pattern::Mu {
            variable: bound,
            body,
        } => connective("\\mu", Vec::new(), vec![variable(bound), one(body)]),
        Pattern::Nu {
            variable: bound,
            body,
        } => connective("\\nu", Vec::new(), vec![variable(bound), one(body)]),
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => connective(
            "\\ceil",
            vec![(**operand_sort).clone(), result_sort.clone()],
            vec![one(argument)],
        ),
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => connective(
            "\\floor",
            vec![(**operand_sort).clone(), result_sort.clone()],
            vec![one(argument)],
        ),
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => connective(
            "\\equals",
            vec![(**operand_sort).clone(), result_sort.clone()],
            vec![one(left), one(right)],
        ),
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => connective(
            "\\in",
            vec![(**operand_sort).clone(), result_sort.clone()],
            vec![one(left), one(right)],
        ),
        Pattern::DomainValue { sort, value } => connective(
            "\\dv",
            vec![sort.clone()],
            vec![Node::Str(value.as_bytes().to_vec())],
        ),
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => associative(*associativity, symbol, &many(arguments)),
    }
}

/// `kore_composite_pattern::desugar_associative`.
fn associative(associativity: Associativity, symbol: &Symbol, arguments: &[Node]) -> Node {
    let sym = || Sym::new(symbol.name.clone(), symbol.sort_parameters.clone());
    let Some((first, rest)) = arguments.split_first() else {
        return Node::app(sym(), Vec::new());
    };
    match associativity {
        Associativity::Left => rest.iter().fold(first.clone(), |accumulated, argument| {
            Node::app(sym(), vec![accumulated, argument.clone()])
        }),
        Associativity::Right => {
            let (last, init) = arguments.split_last().expect("arguments are not empty");
            init.iter()
                .rev()
                .fold(last.clone(), |accumulated, argument| {
                    Node::app(sym(), vec![argument.clone(), accumulated])
                })
        }
    }
}

/// Convert back to KORE, for the KAST fallback of a term without a printable production.
pub(crate) fn to_pattern(node: &Node) -> Option<Pattern> {
    Some(match node {
        Node::Str(bytes) => {
            Pattern::String(k_rust::kore::ast::KoreString::from_bytes(bytes.clone()))
        }
        Node::Var { name, set, sort } => Pattern::Variable(Variable {
            kind: if *set {
                VariableKind::Set
            } else {
                VariableKind::Element
            },
            name: name.clone(),
            sort: sort.clone(),
        }),
        Node::App(app) => {
            let args = app
                .args
                .iter()
                .map(to_pattern)
                .collect::<Option<Vec<_>>>()?;
            connective_pattern(&app.sym, args)?
        }
    })
}

fn bound(node: &Pattern) -> Option<Box<Variable>> {
    match node {
        Pattern::Variable(variable) => Some(Box::new(variable.clone())),
        _ => None,
    }
}

#[expect(
    clippy::too_many_lines,
    reason = "one arm per matching-logic connective, the inverse of `from_pattern`"
)]
fn connective_pattern(sym: &Sym, args: Vec<Pattern>) -> Option<Pattern> {
    let sort = || sym.formals.first().cloned();
    let pair = |args: Vec<Pattern>| -> Option<(Box<Pattern>, Box<Pattern>)> {
        let [left, right] = <[Pattern; 2]>::try_from(args).ok()?;
        Some((Box::new(left), Box::new(right)))
    };
    let single = |args: Vec<Pattern>| -> Option<Box<Pattern>> {
        let [argument] = <[Pattern; 1]>::try_from(args).ok()?;
        Some(Box::new(argument))
    };
    let two_sorts = || -> Option<(Box<Sort>, Sort)> {
        Some((
            Box::new(sym.formals.first()?.clone()),
            sym.formals.get(1)?.clone(),
        ))
    };
    Some(match sym.name.as_str() {
        "\\top" => Pattern::Top { sort: sort()? },
        "\\bottom" => Pattern::Bottom { sort: sort()? },
        "\\and" => Pattern::And {
            sort: sort()?,
            arguments: args,
        },
        "\\or" => Pattern::Or {
            sort: sort()?,
            arguments: args,
        },
        "\\not" => Pattern::Not {
            sort: sort()?,
            argument: single(args)?,
        },
        "\\next" => Pattern::Next {
            sort: sort()?,
            argument: single(args)?,
        },
        "\\implies" | "\\iff" | "\\rewrites" => {
            let (left, right) = pair(args)?;
            let sort = sort()?;
            match sym.name.as_str() {
                "\\implies" => Pattern::Implies { sort, left, right },
                "\\iff" => Pattern::Iff { sort, left, right },
                _ => Pattern::Rewrites { sort, left, right },
            }
        }
        "\\exists" | "\\forall" | "\\mu" | "\\nu" => {
            let (variable, body) = pair(args)?;
            let variable = bound(&variable)?;
            match sym.name.as_str() {
                "\\exists" => Pattern::Exists {
                    sort: sort()?,
                    variable,
                    body,
                },
                "\\forall" => Pattern::Forall {
                    sort: sort()?,
                    variable,
                    body,
                },
                "\\mu" => Pattern::Mu { variable, body },
                _ => Pattern::Nu { variable, body },
            }
        }
        "\\ceil" | "\\floor" => {
            let (operand_sort, result_sort) = two_sorts()?;
            let argument = single(args)?;
            if sym.name == "\\ceil" {
                Pattern::Ceil {
                    operand_sort,
                    result_sort,
                    argument,
                }
            } else {
                Pattern::Floor {
                    operand_sort,
                    result_sort,
                    argument,
                }
            }
        }
        "\\equals" | "\\in" => {
            let (operand_sort, result_sort) = two_sorts()?;
            let (left, right) = pair(args)?;
            if sym.name == "\\equals" {
                Pattern::Equals {
                    operand_sort,
                    result_sort,
                    left,
                    right,
                }
            } else {
                Pattern::In {
                    operand_sort,
                    result_sort,
                    left,
                    right,
                }
            }
        }
        "\\dv" => {
            let Pattern::String(value) = &*single(args)? else {
                return None;
            };
            let value = value.clone();
            Pattern::DomainValue {
                sort: sort()?,
                value,
            }
        }
        _ => Pattern::Application {
            symbol: Symbol {
                name: sym.name.clone(),
                sort_parameters: sym.formals.clone(),
            },
            arguments: args,
        },
    })
}

/// A symbol declaration: its sort parameters, argument sorts and result sort.
#[derive(Clone, Debug)]
pub(crate) struct Declaration {
    pub parameters: Vec<String>,
    pub arguments: Vec<Sort>,
    pub result: Sort,
}

/// `kore_symbol::instantiate_symbol` on every non-builtin symbol of `node`.
pub(crate) fn instantiate(node: &mut Node, declarations: &BTreeMap<String, Declaration>) {
    let mut stack = vec![node];
    // Invariant: every node popped is instantiated once and pushes only its own children.
    while let Some(node) = stack.pop() {
        if let Node::App(app) = node {
            instantiate_symbol(&mut app.sym, declarations);
            stack.extend(app.args.iter_mut());
        }
    }
}

pub(crate) fn instantiate_symbol(sym: &mut Sym, declarations: &BTreeMap<String, Declaration>) {
    if sym.is_builtin() || !sym.arguments.is_empty() || sym.sort.is_some() {
        return;
    }
    let Some(declaration) = declarations.get(&sym.name) else {
        return;
    };
    let substitution = declaration
        .parameters
        .iter()
        .cloned()
        .zip(sym.formals.iter().cloned())
        .collect::<BTreeMap<_, _>>();
    sym.arguments = declaration
        .arguments
        .iter()
        .map(|sort| substitute_sort(sort, &substitution))
        .collect();
    sym.sort = Some(substitute_sort(&declaration.result, &substitution));
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<String, Sort>) -> Sort {
    match sort {
        Sort::Variable(name) => substitution
            .get(name)
            .cloned()
            .unwrap_or_else(|| sort.clone()),
        Sort::Application { name, arguments } => Sort::Application {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_sort(argument, substitution))
                .collect(),
        },
    }
}
