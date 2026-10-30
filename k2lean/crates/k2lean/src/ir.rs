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
    /// Replace the argument of every `name("...")` with `value`.
    pub fn set_string(&mut self, name: &str, value: &str) {
        for p in &mut self.0 {
            if let P::App(n, _, args) = p
                && n == name
            {
                *args = vec![P::Str(value.to_string())];
            }
        }
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
    out.axioms = split_alternatives(std::mem::take(&mut out.axioms));
    Ok(out)
}

/// Most axioms one axiom is split into; an axiom with more alternatives stays whole.
const MAX_ALTERNATIVES: usize = 256;

/// Each axiom whose matched patterns contain `\or` replaced by one axiom per alternative.
///
/// A rewrite axiom `\or(A, B) ∧ φ ⇒ R` denotes the union of the transitions of `A ∧ φ ⇒ R` and
/// `B ∧ φ ⇒ R`, and an equation `\or(A, B) → f(…) = e` is the conjunction of `A → f(…) = e` and
/// `B → f(…) = e`, every variable quantified over each as over the whole; an equation's guard
/// against its competitors is the negation of their applicability, which is the same for the
/// whole and the conjunction of its parts. So the split denotes the same theory, and the
/// lowering never meets an `\or` in a left-hand side. The matched patterns are a rewrite's
/// left-hand side and an equation's left-hand side and argument patterns (`\in(X, P)`); a
/// disjunction of predicates (in a requires) is a predicate and stays whole.
///
/// The `k`-th alternative's `label` and `UNIQUE'Unds'ID` get the suffix `_ork` (a fresh name
/// when that one is taken), so that its rule and equation names are its own; its `index` is its
/// position among the split axioms, so the alternatives stay where the axiom was in sentence
/// order. A definition with no such `\or` is returned unchanged, indices included.
fn split_alternatives(axioms: Vec<AxiomDecl>) -> Vec<AxiomDecl> {
    let split: Vec<Vec<P>> = axioms.iter().map(|a| alternatives(&a.pattern)).collect();
    if split.iter().all(|alts| alts.len() <= 1) {
        return axioms;
    }
    let mut taken: std::collections::BTreeSet<String> = axioms
        .iter()
        .flat_map(|a| [a.attrs.string("label"), a.attrs.string(UNIQUE_ID)])
        .flatten()
        .collect();
    let mut out = Vec::new();
    for (a, alts) in axioms.into_iter().zip(split) {
        if alts.len() <= 1 {
            out.push(AxiomDecl {
                index: out.len() + 1,
                ..a
            });
            continue;
        }
        for (k, pattern) in alts.into_iter().enumerate() {
            let mut attrs = a.attrs.clone();
            for key in ["label", UNIQUE_ID] {
                if let Some(name) = a.attrs.string(key) {
                    let mut fresh = format!("{name}_or{}", k + 1);
                    while !taken.insert(fresh.clone()) {
                        fresh.push('_');
                    }
                    attrs.set_string(key, &fresh);
                }
            }
            out.push(AxiomDecl {
                params: a.params.clone(),
                pattern,
                attrs,
                module: a.module.clone(),
                index: out.len() + 1,
            });
        }
    }
    out
}

const UNIQUE_ID: &str = "UNIQUE'Unds'ID";

/// The alternatives of an axiom (itself alone when it has none, or more than
/// [`MAX_ALTERNATIVES`]).
fn alternatives(p: &P) -> Vec<P> {
    let alts = match p {
        P::Rewrites(s, l, r) => matched(l).map(|ls| {
            ls.into_iter()
                .map(|l| P::Rewrites(s.clone(), Box::new(l), r.clone()))
                .collect()
        }),
        P::Implies(s, l, r) => {
            let rights = match &**r {
                P::Equals(os, rs, lhs, rhs) => matched(lhs).map(|lhss| {
                    lhss.into_iter()
                        .map(|lhs| P::Equals(os.clone(), rs.clone(), Box::new(lhs), rhs.clone()))
                        .collect()
                }),
                other => Some(vec![other.clone()]),
            };
            match (binders(l), rights) {
                (Some(ls), Some(rs)) => product(vec![ls, rs]).map(|pairs| {
                    pairs
                        .into_iter()
                        .map(|mut lr| {
                            let r = lr.pop().expect("a right part");
                            let l = lr.pop().expect("a left part");
                            P::Implies(s.clone(), Box::new(l), Box::new(r))
                        })
                        .collect()
                }),
                _ => None,
            }
        }
        _ => None,
    };
    alts.unwrap_or_else(|| vec![p.clone()])
}

/// The alternatives of a claim `\implies(φ ∧ L, ◇R)`: one per disjunct of each `\or` in its
/// left-hand side `L` (itself alone when it has none, or more than [`MAX_ALTERNATIVES`]). The
/// claim holds exactly where each alternative does, as an axiom's alternatives do
/// ([`split_alternatives`]).
pub fn claim_alternatives(p: &P) -> Vec<P> {
    let P::Implies(s, l, r) = p else {
        return vec![p.clone()];
    };
    match matched(l) {
        Some(ls) => ls
            .into_iter()
            .map(|l| P::Implies(s.clone(), Box::new(l), r.clone()))
            .collect(),
        None => vec![p.clone()],
    }
}

/// A claim `\implies(φ ∧ L, ◇R)` with each alias `\and(t, X)` of a ground term `t` in its
/// left-hand side `L` replaced by `t`, and `X` by `t` everywhere else: the alias denotes `t` where
/// `X = t` and nothing elsewhere, so the claim says the same of every instance (`t` is ground, so
/// no binder of the claim captures it). Other aliases stay.
pub fn inline_aliases(p: &P) -> P {
    let P::Implies(s, l, r) = p else {
        return p.clone();
    };
    let mut aliases = BTreeMap::new();
    let l = unalias(l, &mut aliases);
    if aliases.is_empty() {
        return p.clone();
    }
    substitute(&P::Implies(s.clone(), Box::new(l), r.clone()), &aliases)
}

fn unalias(p: &P, aliases: &mut BTreeMap<String, P>) -> P {
    match p {
        P::And(s, ps) => {
            if let [a, b] = ps.as_slice() {
                let (var, term) = match (a, b) {
                    (P::Var(v, _), t) | (t, P::Var(v, _)) => (Some(v), t),
                    _ => (None, a),
                };
                if let Some(v) = var
                    && matches!(term, P::App(..) | P::Dv(..) | P::Str(_))
                    && ground(term)
                    && !aliases.contains_key(v)
                {
                    aliases.insert(v.clone(), term.clone());
                    return term.clone();
                }
            }
            P::And(s.clone(), ps.iter().map(|q| unalias(q, aliases)).collect())
        }
        P::App(f, s, args) => P::App(
            f.clone(),
            s.clone(),
            args.iter().map(|q| unalias(q, aliases)).collect(),
        ),
        _ => p.clone(),
    }
}

fn ground(p: &P) -> bool {
    let mut vars = false;
    visit(p, &mut |q| vars |= matches!(q, P::Var(..) | P::SetVar(..)));
    !vars
}

fn visit(p: &P, f: &mut impl FnMut(&P)) {
    f(p);
    match p {
        P::App(_, _, ps) | P::And(_, ps) | P::Or(_, ps) => ps.iter().for_each(|q| visit(q, f)),
        P::Not(_, a)
        | P::Ceil(_, _, a)
        | P::Floor(_, _, a)
        | P::Exists(_, _, _, a)
        | P::Forall(_, _, _, a) => visit(a, f),
        P::Implies(_, a, b)
        | P::Iff(_, a, b)
        | P::Rewrites(_, a, b)
        | P::Equals(_, _, a, b)
        | P::In(_, _, a, b) => {
            visit(a, f);
            visit(b, f)
        }
        P::Str(_)
        | P::Var(..)
        | P::SetVar(..)
        | P::Dv(..)
        | P::Top(_)
        | P::Bottom(_)
        | P::Other(_) => {}
    }
}

/// `p` with each free element variable of `s` replaced by its term.
fn substitute(p: &P, s: &BTreeMap<String, P>) -> P {
    let all = |ps: &[P]| ps.iter().map(|q| substitute(q, s)).collect();
    let one = |a: &P| Box::new(substitute(a, s));
    match p {
        P::Var(v, _) => s.get(v).cloned().unwrap_or_else(|| p.clone()),
        P::App(f, ss, ps) => P::App(f.clone(), ss.clone(), all(ps)),
        P::And(x, ps) => P::And(x.clone(), all(ps)),
        P::Or(x, ps) => P::Or(x.clone(), all(ps)),
        P::Not(x, a) => P::Not(x.clone(), one(a)),
        P::Ceil(x, y, a) => P::Ceil(x.clone(), y.clone(), one(a)),
        P::Floor(x, y, a) => P::Floor(x.clone(), y.clone(), one(a)),
        P::Implies(x, a, b) => P::Implies(x.clone(), one(a), one(b)),
        P::Iff(x, a, b) => P::Iff(x.clone(), one(a), one(b)),
        P::Rewrites(x, a, b) => P::Rewrites(x.clone(), one(a), one(b)),
        P::Equals(x, y, a, b) => P::Equals(x.clone(), y.clone(), one(a), one(b)),
        P::In(x, y, a, b) => P::In(x.clone(), y.clone(), one(a), one(b)),
        P::Exists(x, v, vs, a) | P::Forall(x, v, vs, a) => {
            let mut inner = s.clone();
            inner.remove(v);
            let body = Box::new(substitute(a, &inner));
            if matches!(p, P::Exists(..)) {
                P::Exists(x.clone(), v.clone(), vs.clone(), body)
            } else {
                P::Forall(x.clone(), v.clone(), vs.clone(), body)
            }
        }
        P::Str(_) | P::SetVar(..) | P::Dv(..) | P::Top(_) | P::Bottom(_) | P::Other(_) => p.clone(),
    }
}

/// A matched term with each `\or` resolved to one of its disjuncts, in every combination; `None`
/// beyond [`MAX_ALTERNATIVES`]. A predicate (`\equals`, `\ceil`, `\not`, …) is not descended into.
fn matched(p: &P) -> Option<Vec<P>> {
    match p {
        P::Or(_, ps) => {
            let mut out = Vec::new();
            for q in ps {
                out.extend(matched(q)?);
                if out.len() > MAX_ALTERNATIVES {
                    return None;
                }
            }
            Some(out)
        }
        P::App(f, s, args) => Some(
            product(args.iter().map(matched).collect::<Option<_>>()?)?
                .into_iter()
                .map(|args| P::App(f.clone(), s.clone(), args))
                .collect(),
        ),
        P::And(s, ps) => Some(
            product(ps.iter().map(matched).collect::<Option<_>>()?)?
                .into_iter()
                .map(|ps| P::And(s.clone(), ps))
                .collect(),
        ),
        _ => Some(vec![p.clone()]),
    }
}

/// An equation's antecedent with the alternatives of its argument patterns (`\in(X, P)`).
fn binders(p: &P) -> Option<Vec<P>> {
    match p {
        P::And(s, ps) => Some(
            product(ps.iter().map(binders).collect::<Option<_>>()?)?
                .into_iter()
                .map(|ps| P::And(s.clone(), ps))
                .collect(),
        ),
        P::In(os, rs, x, q) => Some(
            matched(q)?
                .into_iter()
                .map(|q| P::In(os.clone(), rs.clone(), x.clone(), Box::new(q)))
                .collect(),
        ),
        _ => Some(vec![p.clone()]),
    }
}

/// Every choice of one element from each list, in order; `None` beyond [`MAX_ALTERNATIVES`].
fn product(choices: Vec<Vec<P>>) -> Option<Vec<Vec<P>>> {
    let size = choices
        .iter()
        .try_fold(1usize, |n, c| n.checked_mul(c.len()))?;
    if size > MAX_ALTERNATIVES {
        return None;
    }
    let mut out = vec![Vec::new()];
    for choice in choices {
        out = out
            .into_iter()
            .flat_map(|prefix| {
                choice.iter().map(move |c| {
                    let mut next = prefix.clone();
                    next.push(c.clone());
                    next
                })
            })
            .collect();
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    //! The split of left-hand-side disjunctions (`split_alternatives`), on the `orpat` fixture.
    use super::*;
    use crate::funcs::tests::fixture;
    use std::collections::BTreeSet;

    #[test]
    fn left_hand_side_disjunctions_become_one_axiom_per_alternative() {
        let def = fixture("orpat");
        assert!(
            def.axioms
                .iter()
                .all(|a| alternatives(&a.pattern).len() == 1),
            "a matched disjunction survived the split"
        );
        assert!(def.axioms.windows(2).all(|w| w[0].index < w[1].index));
        let labels: Vec<String> = def
            .axioms
            .iter()
            .filter_map(|a| a.attrs.string("label"))
            .filter(|l| l.starts_with("step"))
            .collect();
        assert_eq!(labels, ["step_or1", "step_or2"]);
        let names = crate::rulename::assign(&def);
        assert!(names.values().any(|n| n == "step_or1") && names.values().any(|n| n == "step_or2"));
        // `cost`: the two alternatives of its first equation, adjacent in the cascade, then the
        // literal row, then the owise row.
        let cost =
            &crate::funcs::equations(&def)["Lblcost'LParUndsRParUnds'ORPAT'Unds'Int'Unds'Op"];
        let heads: Vec<(Option<&str>, i64)> = cost
            .iter()
            .map(|e| (e.args[0].app_name(), e.priority))
            .collect();
        assert_eq!(
            heads,
            [
                (
                    Some("Lblinc'LParUndsRParUnds'ORPAT-SYNTAX'Unds'Op'Unds'Int"),
                    50
                ),
                (
                    Some("Lbldec'LParUndsRParUnds'ORPAT-SYNTAX'Unds'Op'Unds'Int"),
                    50
                ),
                (Some("Lblnop'Unds'ORPAT-SYNTAX'Unds'Op"), 50),
                (None, 200)
            ]
        );
        let uids: BTreeSet<&str> = cost.iter().map(|e| e.uid.as_str()).collect();
        assert_eq!(uids.len(), cost.len(), "{uids:?}");
        crate::funcs::tests::generated(&def);
    }

    /// `f((1 #Or 2) #as X) => g(X)`: two claims, `f(1) => g(1)` and `f(2) => g(2)`. An alias of a
    /// term with a variable is not inlined.
    #[test]
    fn a_claim_disjunction_is_one_claim_per_alternative_with_its_alias_inlined() {
        let int = S::App("SortInt".into(), vec![]);
        let k = S::App("SortK".into(), vec![]);
        let x = P::Var("VarX".into(), int.clone());
        let lit = |n: &str| P::Dv(int.clone(), n.into());
        let app = |f: &str, a: P| P::App(f.into(), vec![], vec![a]);
        let claim = |arg: P, result: P| {
            P::Implies(
                k.clone(),
                Box::new(P::And(k.clone(), vec![P::Top(k.clone()), app("f", arg)])),
                Box::new(app("weakAlwaysFinally", app("g", result))),
            )
        };
        let or = P::Or(int.clone(), vec![lit("1"), lit("2")]);
        let written = claim(P::And(int.clone(), vec![or, x.clone()]), x.clone());
        let split: Vec<P> = claim_alternatives(&written)
            .iter()
            .map(inline_aliases)
            .collect();
        assert_eq!(
            split,
            [claim(lit("1"), lit("1")), claim(lit("2"), lit("2"))]
        );
        let y = P::Var("VarY".into(), int.clone());
        let open = claim(P::And(int.clone(), vec![app("h", y), x.clone()]), x);
        assert_eq!(claim_alternatives(&open), std::slice::from_ref(&open));
        assert_eq!(inline_aliases(&open), open);
    }

    #[test]
    fn a_definition_without_matched_disjunctions_is_unchanged() {
        let def = fixture("peano");
        assert!(def.axioms.windows(2).all(|w| w[0].index < w[1].index));
        let text = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/peano/definition.kore"),
        )
        .unwrap();
        let parsed = k_rust_kore::kore::parser::parse_definition(&text).unwrap();
        let axioms = parsed
            .modules
            .iter()
            .flat_map(|m| &m.sentences)
            .filter(|s| matches!(s, Sentence::Axiom { .. }))
            .count();
        assert_eq!(def.axioms.len(), axioms);
    }
}
