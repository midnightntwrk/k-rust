//! An owned, simplified view of a KORE definition.
//!
//! The k-rust KORE AST is built for scale (explicit work stacks, `Drop` impls); the generator
//! only needs a small tree it can match on by value, so the parsed definition is converted once.

use k_rust_kore::kore::ast::{self, Pattern, Sentence, Sort};
use std::collections::BTreeMap;

/// A sort: a name applied to arguments, or a sort variable.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum S {
    Var(String),
    App(String, Vec<S>),
}

impl S {
    pub fn name(&self) -> Option<&str> {
        match self {
            S::App(n, a) if a.is_empty() => Some(n),
            _ => None,
        }
    }
}

impl std::fmt::Display for S {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            S::Var(v) => write!(f, "{v}"),
            S::App(n, a) => {
                write!(f, "{n}{{")?;
                for (i, s) in a.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{s}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// A pattern, owned.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum P {
    Str(String),
    Var(String, S),
    SetVar(String, S),
    App(String, Vec<S>, Vec<P>),
    Dv(S, String),
    Top(S),
    Bottom(S),
    And(S, Vec<P>),
    Or(S, Vec<P>),
    Not(S, Box<P>),
    Implies(S, Box<P>, Box<P>),
    Iff(S, Box<P>, Box<P>),
    Rewrites(S, Box<P>, Box<P>),
    Exists(S, String, S, Box<P>),
    Forall(S, String, S, Box<P>),
    Ceil(S, S, Box<P>),
    Floor(S, S, Box<P>),
    Equals(S, S, Box<P>, Box<P>),
    In(S, S, Box<P>, Box<P>),
    /// `\left-assoc`/`\right-assoc` and fixpoints, which the generator never needs to look into.
    Other(String),
}

impl P {
    pub fn app_name(&self) -> Option<&str> {
        match self {
            P::App(n, _, _) => Some(n),
            _ => None,
        }
    }
}

pub fn sort(s: &Sort) -> S {
    match s {
        Sort::Variable(v) => S::Var(v.clone()),
        Sort::Application { name, arguments } => {
            S::App(name.clone(), arguments.iter().map(sort).collect())
        }
    }
}

fn kstr(s: &ast::KoreString) -> String {
    match s.as_utf8() {
        Ok(t) => t.to_string(),
        Err(_) => s.as_bytes().iter().map(|b| *b as char).collect(),
    }
}

pub fn pat(p: &Pattern) -> P {
    match p {
        Pattern::String(s) => P::Str(kstr(s)),
        Pattern::Variable(v) => match v.kind {
            ast::VariableKind::Element => P::Var(v.name.clone(), sort(&v.sort)),
            ast::VariableKind::Set => P::SetVar(v.name.clone(), sort(&v.sort)),
        },
        Pattern::Application { symbol, arguments } => P::App(
            symbol.name.clone(),
            symbol.sort_parameters.iter().map(sort).collect(),
            arguments.iter().map(pat).collect(),
        ),
        Pattern::Top { sort: s } => P::Top(sort(s)),
        Pattern::Bottom { sort: s } => P::Bottom(sort(s)),
        Pattern::And { sort: s, arguments } => P::And(sort(s), arguments.iter().map(pat).collect()),
        Pattern::Or { sort: s, arguments } => P::Or(sort(s), arguments.iter().map(pat).collect()),
        Pattern::Not { sort: s, argument } => P::Not(sort(s), Box::new(pat(argument))),
        Pattern::Next { .. } => P::Other("\\next".into()),
        Pattern::Implies {
            sort: s,
            left,
            right,
        } => P::Implies(sort(s), Box::new(pat(left)), Box::new(pat(right))),
        Pattern::Iff {
            sort: s,
            left,
            right,
        } => P::Iff(sort(s), Box::new(pat(left)), Box::new(pat(right))),
        Pattern::Rewrites {
            sort: s,
            left,
            right,
        } => P::Rewrites(sort(s), Box::new(pat(left)), Box::new(pat(right))),
        Pattern::Exists {
            sort: s,
            variable,
            body,
        } => P::Exists(
            sort(s),
            variable.name.clone(),
            sort(&variable.sort),
            Box::new(pat(body)),
        ),
        Pattern::Forall {
            sort: s,
            variable,
            body,
        } => P::Forall(
            sort(s),
            variable.name.clone(),
            sort(&variable.sort),
            Box::new(pat(body)),
        ),
        Pattern::Mu { .. } => P::Other("\\mu".into()),
        Pattern::Nu { .. } => P::Other("\\nu".into()),
        Pattern::Ceil {
            operand_sort,
            result_sort,
            argument,
        } => P::Ceil(
            sort(operand_sort),
            sort(result_sort),
            Box::new(pat(argument)),
        ),
        Pattern::Floor {
            operand_sort,
            result_sort,
            argument,
        } => P::Floor(
            sort(operand_sort),
            sort(result_sort),
            Box::new(pat(argument)),
        ),
        Pattern::Equals {
            operand_sort,
            result_sort,
            left,
            right,
        } => P::Equals(
            sort(operand_sort),
            sort(result_sort),
            Box::new(pat(left)),
            Box::new(pat(right)),
        ),
        Pattern::In {
            operand_sort,
            result_sort,
            left,
            right,
        } => P::In(
            sort(operand_sort),
            sort(result_sort),
            Box::new(pat(left)),
            Box::new(pat(right)),
        ),
        Pattern::DomainValue { sort: s, value } => P::Dv(sort(s), kstr(value)),
        Pattern::AssociativeApplication {
            associativity,
            symbol,
            arguments,
        } => {
            // `\left-assoc{}(f(a, b, c))` = `f(f(a, b), c)`; `\right-assoc` nests to the right
            let params: Vec<S> = symbol.sort_parameters.iter().map(sort).collect();
            let args: Vec<P> = arguments.iter().map(pat).collect();
            let name = symbol.name.clone();
            let mk = |a: P, b: P| P::App(name.clone(), params.clone(), vec![a, b]);
            match associativity {
                ast::Associativity::Left => {
                    let mut it = args.into_iter();
                    match it.next() {
                        None => P::Other("empty assoc".into()),
                        Some(first) => it.fold(first, mk),
                    }
                }
                ast::Associativity::Right => {
                    let mut it = args.into_iter().rev();
                    match it.next() {
                        None => P::Other("empty assoc".into()),
                        Some(last) => it.fold(last, |acc, a| mk(a, acc)),
                    }
                }
            }
        }
    }
}

/// Attributes: `name(args)` where args are string literals or applications.
#[derive(Clone, Debug, Default)]
pub struct Attrs(pub Vec<P>);

impl Attrs {
    pub fn has(&self, name: &str) -> bool {
        self.0.iter().any(|p| p.app_name() == Some(name))
    }
    pub fn get(&self, name: &str) -> Option<&P> {
        self.0.iter().find(|p| p.app_name() == Some(name))
    }
    /// The single string argument of `name("...")`.
    pub fn string(&self, name: &str) -> Option<String> {
        match self.get(name)? {
            P::App(_, _, args) => match args.first()? {
                P::Str(s) => Some(s.clone()),
                _ => None,
            },
            _ => None,
        }
    }
}

fn attrs(a: &ast::Attributes) -> Attrs {
    Attrs(a.0.iter().map(pat).collect())
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct SortDecl {
    pub name: String,
    pub params: Vec<String>,
    pub hooked: bool,
    pub attrs: Attrs,
    pub module: String,
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct SymbolDecl {
    pub name: String,
    pub params: Vec<String>,
    pub args: Vec<S>,
    pub result: S,
    pub hooked: bool,
    pub attrs: Attrs,
    pub module: String,
}

impl SymbolDecl {
    pub fn hook(&self) -> Option<String> {
        self.attrs.string("hook")
    }
    pub fn is_function(&self) -> bool {
        self.attrs.has("function")
            || self.hooked && self.hook().is_some() && !self.attrs.has("constructor")
    }
}

#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct AxiomDecl {
    pub params: Vec<String>,
    pub pattern: P,
    pub attrs: Attrs,
    pub module: String,
    /// Position in the file (sentence order), used for stable naming.
    pub index: usize,
}

#[derive(Debug, Default)]
#[allow(dead_code)]
pub struct Def {
    pub sorts: BTreeMap<String, SortDecl>,
    pub symbols: BTreeMap<String, SymbolDecl>,
    pub axioms: Vec<AxiomDecl>,
    pub attrs: Attrs,
}

pub fn load(text: &str) -> Result<Def, String> {
    let d = k_rust_kore::kore::parser::parse_definition(text).map_err(|e| format!("{e:?}"))?;
    let mut out = Def {
        attrs: attrs(&d.attributes),
        ..Default::default()
    };
    let mut index = 0usize;
    for m in &d.modules {
        for s in &m.sentences {
            index += 1;
            match s {
                Sentence::SortDeclaration {
                    hooked,
                    name,
                    parameters,
                    attributes,
                } => {
                    out.sorts.insert(
                        name.clone(),
                        SortDecl {
                            name: name.clone(),
                            params: parameters.clone(),
                            hooked: *hooked,
                            attrs: attrs(attributes),
                            module: m.name.clone(),
                        },
                    );
                }
                Sentence::SymbolDeclaration {
                    hooked,
                    symbol,
                    argument_sorts,
                    result_sort,
                    attributes,
                } => {
                    let params = symbol
                        .sort_parameters
                        .iter()
                        .map(|p| match p {
                            Sort::Variable(v) => v.clone(),
                            Sort::Application { name, .. } => name.clone(),
                        })
                        .collect();
                    out.symbols.insert(
                        symbol.name.clone(),
                        SymbolDecl {
                            name: symbol.name.clone(),
                            params,
                            args: argument_sorts.iter().map(sort).collect(),
                            result: sort(result_sort),
                            hooked: *hooked,
                            attrs: attrs(attributes),
                            module: m.name.clone(),
                        },
                    );
                }
                Sentence::Axiom {
                    parameters,
                    pattern,
                    attributes,
                } => out.axioms.push(AxiomDecl {
                    params: parameters.clone(),
                    pattern: pat(pattern),
                    attrs: attrs(attributes),
                    module: m.name.clone(),
                    index,
                }),
                Sentence::Import { .. }
                | Sentence::AliasDeclaration { .. }
                | Sentence::Claim { .. } => {}
            }
        }
    }
    Ok(out)
}
