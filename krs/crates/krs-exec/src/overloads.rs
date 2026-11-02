//! The definition's overload axioms, by which the read-back compares a print with the state.
//!
//! K states an overload (`syntax Vals ::= List{Val, ","} [overload(Exps)]`, the `Exps` overload
//! of K's `Vals` idiom) by one axiom per pair of a greater symbol and its more specific
//! overload:
//!
//! ```text
//! axiom{R} \equals{SortExps{}, R}(
//!     LblexpsCons{}(inj{SortVal{}, SortExp{}}(K0:SortVal{}), inj{SortVals{}, SortExps{}}(K1:SortVals{})),
//!     inj{SortVals{}, SortExps{}}(LblvalsCons{}(K0:SortVal{}, K1:SortVals{}))
//! ) [symbol-overload{}(LblexpsCons{}(), LblvalsCons{}())]
//! ```
//!
//! The two sides are one term of the definition, but only where the greater symbol's arguments
//! are injections from the overload's argument sorts: `expsCons(tick, ..)`, whose `tick` is an
//! `Exp` and no `Val`, is no `valsCons`. A reader builds a term as the grammar reads its text
//! (`tick , 2` is an `Exps` list throughout), where a run that evaluated a part holds its more
//! specific overload (`expsCons(tick, inj(valsCons(2, valsNil)))`), so both sides of a
//! comparison are rewritten by the axioms, left to right, wherever a greater symbol's arguments
//! match, until none matches ([`Overloads::normalize`]), and then compared exactly.
//!
//! The axioms are the backend's stored axioms that carry `symbol-overload`. Matching an
//! argument `inj{L, G}(K:L)` takes any injection `inj{S, G}(t)` whose sort `S` is `L` or below it
//! (injections compose: `inj{S, G}(t)` is `inj{L, G}(inj{S, L}(t))`), by the definition's
//! `subsort` axioms; an injection of an injection is one injection.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use k_rust::k_rust_backend::definition::PendingAxiom;
use k_rust::kore::ast::{Pattern, Sort, Symbol, Variable};

/// The overload axioms of one definition, oriented towards the more specific overload.
#[derive(Clone, Debug, Default)]
pub(crate) struct Overloads {
    /// Each axiom's two sides, by the greater symbol its left side applies, in a fixed order.
    axioms: BTreeMap<String, Vec<(Pattern, Pattern)>>,
    /// Each sort and the sorts strictly below it, by the `subsort` axioms' closure; built only
    /// where the definition has an overload axiom.
    below: BTreeMap<Sort, BTreeSet<Sort>>,
}

impl Overloads {
    /// The overload axioms among `axioms`, the backend's stored axioms.
    pub(crate) fn new(axioms: &[PendingAxiom]) -> Self {
        let mut overloads = Self::default();
        for axiom in axioms {
            if !axiom
                .attributes
                .0
                .iter()
                .any(|attribute| attribute_name(attribute) == Some("symbol-overload"))
            {
                continue;
            }
            let Pattern::Equals { left, right, .. } = &axiom.pattern else {
                continue;
            };
            let Pattern::Application { symbol, .. } = &**left else {
                continue;
            };
            overloads
                .axioms
                .entry(symbol.name.clone())
                .or_default()
                .push(((**left).clone(), (**right).clone()));
        }
        for sides in overloads.axioms.values_mut() {
            sides.sort();
        }
        if overloads.axioms.is_empty() {
            return overloads;
        }
        let mut pairs = BTreeSet::new();
        for axiom in axioms {
            for attribute in &axiom.attributes.0 {
                if let Pattern::Application { symbol, .. } = attribute
                    && attribute_name(attribute) == Some("subsort")
                    && let [sub, sup] = symbol.sort_parameters.as_slice()
                {
                    pairs.insert((sup.clone(), sub.clone()));
                }
            }
        }
        // The transitive closure: each round adds the pairs one step longer, until none.
        loop {
            let longer = pairs
                .iter()
                .flat_map(|(sup, middle)| {
                    pairs
                        .iter()
                        .filter(move |(other, _)| other == middle)
                        .map(move |(_, sub)| (sup.clone(), sub.clone()))
                })
                .filter(|pair| !pairs.contains(pair))
                .collect::<Vec<_>>();
            if longer.is_empty() {
                break;
            }
            pairs.extend(longer);
        }
        for (sup, sub) in pairs {
            overloads.below.entry(sup).or_default().insert(sub);
        }
        overloads
    }

    /// `pattern` with every application the overload axioms rewrite replaced, inside out and
    /// again on what they write, by the more specific overload the axiom states; where several
    /// axioms of one symbol match, the first in a fixed order. Without an overload axiom,
    /// `pattern` itself.
    ///
    /// A `\left-assoc{}`/`\right-assoc{}` application (an abbreviation of nested binary
    /// applications, which only the KORE text and JSON readers build; neither a backend state
    /// nor a parser's reading holds one) is not rewritten at its own symbol, only inside its
    /// arguments: a comparison of two terms that differ there by an axiom then fails, so that
    /// a print it judges is never taken for the term without the axioms saying so.
    pub(crate) fn normalize<'p>(&self, pattern: &'p Pattern) -> Cow<'p, Pattern> {
        if self.axioms.is_empty() {
            return Cow::Borrowed(pattern);
        }
        Cow::Owned(self.rewrite(pattern.clone()))
    }

    /// `pattern`, normal below its root, rewritten at its root and inside out below: each
    /// argument first, then the application. The values an axiom binds are normal already, so
    /// only the application the axiom writes is rewritten again ([`Self::write`]); every part of
    /// the term is moved, not copied.
    fn rewrite(&self, mut pattern: Pattern) -> Pattern {
        match &mut pattern {
            Pattern::Application { symbol, arguments } => {
                let arguments = std::mem::take(arguments)
                    .into_iter()
                    .map(|argument| self.rewrite(argument))
                    .collect();
                self.at_root(std::mem::replace(symbol, placeholder_symbol()), arguments)
            }
            Pattern::AssociativeApplication { arguments, .. } => {
                let rewritten = std::mem::take(arguments)
                    .into_iter()
                    .map(|argument| self.rewrite(argument))
                    .collect();
                *arguments = rewritten;
                pattern
            }
            _ => pattern,
        }
    }

    /// The application of `symbol` to `arguments`, each normal, rewritten by the first axiom
    /// that matches it, and again on what the axiom writes, until none matches.
    fn at_root(&self, symbol: Symbol, mut arguments: Vec<Pattern>) -> Pattern {
        if symbol.name == "inj" {
            return injection(&symbol, arguments);
        }
        for (left, right) in self.axioms.get(&symbol.name).into_iter().flatten() {
            let Pattern::Application {
                symbol: wanted,
                arguments: patterns,
            } = left
            else {
                continue;
            };
            let mut bound = BTreeMap::new();
            if *wanted != symbol
                || patterns.len() != arguments.len()
                || !patterns.iter().zip(&arguments).enumerate().all(
                    |(index, (pattern, argument))| {
                        self.matches(pattern, argument, vec![index], &mut bound)
                    },
                )
            {
                continue;
            }
            let bound = bound
                .into_iter()
                .map(|(variable, binding)| (variable, binding.path, binding.injection))
                .collect::<Vec<_>>();
            let mut values = BTreeMap::new();
            for (variable, path, injected) in bound {
                let mut value = take(&mut arguments, &path);
                if let Some(symbol) = injected {
                    value = injection(&symbol, vec![value]);
                }
                values.insert(variable, value);
            }
            let mut uses = BTreeMap::new();
            count_variables(right, &mut uses);
            return self.write(right, &mut values, &mut uses);
        }
        Pattern::Application { symbol, arguments }
    }

    /// `pattern`, an overload axiom's right side, with its variables replaced by `values`, which
    /// are normal, and each application it writes rewritten at its root ([`Self::at_root`]).
    /// `uses` counts the occurrences of each variable still to write: a value is copied for
    /// each but the last.
    fn write(
        &self,
        pattern: &Pattern,
        values: &mut BTreeMap<Variable, Pattern>,
        uses: &mut BTreeMap<Variable, usize>,
    ) -> Pattern {
        match pattern {
            Pattern::Variable(variable) => {
                let left = uses.get_mut(variable).map_or(0, |uses| {
                    *uses -= 1;
                    *uses
                });
                let value = if left > 0 {
                    values.get(variable).cloned()
                } else {
                    values.remove(variable)
                };
                value.unwrap_or_else(|| pattern.clone())
            }
            Pattern::Application { symbol, arguments } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.write(argument, values, uses))
                    .collect();
                self.at_root(symbol.clone(), arguments)
            }
            other => other.clone(),
        }
    }

    /// Whether `term`, standing at `path` among the arguments of an application, is an instance
    /// of `pattern`, an argument of an overload axiom's left side, binding its variables in
    /// `bound` to where their values stand.
    fn matches<'t>(
        &self,
        pattern: &Pattern,
        term: &'t Pattern,
        path: Vec<usize>,
        bound: &mut BTreeMap<Variable, Binding<'t>>,
    ) -> bool {
        match (pattern, term) {
            (Pattern::Variable(variable), term) => bind(
                bound,
                variable,
                Binding {
                    path,
                    term,
                    injection: None,
                },
            ),
            (
                Pattern::Application {
                    symbol: injected,
                    arguments: inner,
                },
                term,
            ) if injected.name == "inj" => {
                let ([Pattern::Variable(variable)], [lesser, greater]) =
                    (inner.as_slice(), injected.sort_parameters.as_slice())
                else {
                    return false;
                };
                let Pattern::Application { symbol, arguments } = term else {
                    return false;
                };
                let ([argument], [sort, target]) =
                    (arguments.as_slice(), symbol.sort_parameters.as_slice())
                else {
                    return false;
                };
                if symbol.name != "inj" || target != greater {
                    return false;
                }
                let injection = if sort == lesser {
                    None
                } else if self.is_below(sort, lesser) {
                    Some(Symbol {
                        name: "inj".to_owned(),
                        sort_parameters: vec![sort.clone(), lesser.clone()],
                    })
                } else {
                    return false;
                };
                let mut path = path;
                path.push(0);
                bind(
                    bound,
                    variable,
                    Binding {
                        path,
                        term: argument,
                        injection,
                    },
                )
            }
            (
                Pattern::Application {
                    symbol: wanted,
                    arguments: patterns,
                },
                Pattern::Application { symbol, arguments },
            ) => {
                wanted == symbol
                    && patterns.len() == arguments.len()
                    && patterns.iter().zip(arguments).enumerate().all(
                        |(index, (pattern, argument))| {
                            let mut path = path.clone();
                            path.push(index);
                            self.matches(pattern, argument, path, bound)
                        },
                    )
            }
            (pattern, term) => pattern == term,
        }
    }

    /// Whether `sub` is strictly below `sup` by the definition's `subsort` axioms.
    fn is_below(&self, sub: &Sort, sup: &Sort) -> bool {
        self.below.get(sup).is_some_and(|below| below.contains(sub))
    }
}

fn attribute_name(attribute: &Pattern) -> Option<&str> {
    match attribute {
        Pattern::Application { symbol, .. } => Some(&symbol.name),
        _ => None,
    }
}

/// Where a variable's value stands in the term an axiom matched: the path to it among the
/// application's arguments, the value, and the injection it is taken under (`inj{S, L}` where
/// the axiom's `inj{L, G}` matched an `inj{S, G}`).
struct Binding<'t> {
    path: Vec<usize>,
    term: &'t Pattern,
    injection: Option<Symbol>,
}

/// Bind `variable` as `binding` says, or check a binding it already has: the same value under
/// the same injection.
fn bind<'t>(
    bound: &mut BTreeMap<Variable, Binding<'t>>,
    variable: &Variable,
    binding: Binding<'t>,
) -> bool {
    if let Some(known) = bound.get(variable) {
        return known.term == binding.term && known.injection == binding.injection;
    }
    bound.insert(variable.clone(), binding);
    true
}

/// The subterm at `path` among `arguments`, moved out; what is left there is never read again.
fn take(arguments: &mut [Pattern], path: &[usize]) -> Pattern {
    let mut slot = &mut arguments[path[0]];
    for &index in &path[1..] {
        let Pattern::Application { arguments, .. } = slot else {
            unreachable!("a path the match took")
        };
        slot = &mut arguments[index];
    }
    std::mem::replace(
        slot,
        Pattern::Top {
            sort: Sort::Variable(String::new()),
        },
    )
}

/// A symbol to leave behind where one is moved out of a pattern that is not read again.
const fn placeholder_symbol() -> Symbol {
    Symbol {
        name: String::new(),
        sort_parameters: Vec::new(),
    }
}

/// Count each variable's occurrences in `pattern` into `uses`.
fn count_variables(pattern: &Pattern, uses: &mut BTreeMap<Variable, usize>) {
    match pattern {
        Pattern::Variable(variable) => *uses.entry(variable.clone()).or_default() += 1,
        Pattern::Application { arguments, .. } => {
            for argument in arguments {
                count_variables(argument, uses);
            }
        }
        _ => {}
    }
}

/// The injection `symbol` (`inj{A, B}`) of `arguments`, an injection of an injection
/// (`inj{A, B}(inj{S, A}(t))`) being the one injection `inj{S, B}(t)`.
fn injection(symbol: &Symbol, mut arguments: Vec<Pattern>) -> Pattern {
    if let ([Pattern::Application { symbol: inner, .. }], [_, target]) =
        (arguments.as_slice(), symbol.sort_parameters.as_slice())
        && inner.name == "inj"
        && let [source, _] = inner.sort_parameters.as_slice()
    {
        let symbol = Symbol {
            name: "inj".to_owned(),
            sort_parameters: vec![source.clone(), target.clone()],
        };
        let Some(Pattern::Application {
            arguments: inner, ..
        }) = arguments.first_mut()
        else {
            unreachable!("an injection")
        };
        return Pattern::Application {
            symbol,
            arguments: std::mem::take(inner),
        };
    }
    Pattern::Application {
        symbol: symbol.clone(),
        arguments,
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use k_rust::backend::{Backend, BackendOptions};
    use k_rust::kore::parser::parse_pattern;

    use super::Overloads;

    /// K's `Vals` idiom in KORE: `Vals` overloads `Exps`, `Val` is below `Exp`, `Int` below
    /// `Val`, and `tick` is an `Exp` that is no `Val`.
    pub(crate) const VALS: &str = r"[]
        module MAIN
            sort SortInt{} []
            sort SortExp{} []
            sort SortVal{} []
            sort SortExps{} []
            sort SortVals{} []
            symbol inj{From, To}(From) : To [sortInjection{}()]
            symbol one{}() : SortInt{} [constructor{}(), functional{}(), injective{}()]
            symbol tick{}() : SortExp{} [constructor{}(), functional{}(), injective{}()]
            symbol expsNil{}() : SortExps{} [constructor{}(), functional{}(), injective{}()]
            symbol expsCons{}(SortExp{}, SortExps{}) : SortExps{} [constructor{}(), functional{}(), injective{}()]
            symbol valsNil{}() : SortVals{} [constructor{}(), functional{}(), injective{}()]
            symbol valsCons{}(SortVal{}, SortVals{}) : SortVals{} [constructor{}(), functional{}(), injective{}()]
            axiom{R} \exists{R}(Val:SortVal{}, \equals{SortVal{}, R}(Val:SortVal{}, inj{SortInt{}, SortVal{}}(From:SortInt{}))) [subsort{SortInt{}, SortVal{}}()]
            axiom{R} \exists{R}(Val:SortExp{}, \equals{SortExp{}, R}(Val:SortExp{}, inj{SortVal{}, SortExp{}}(From:SortVal{}))) [subsort{SortVal{}, SortExp{}}()]
            axiom{R} \exists{R}(Val:SortExps{}, \equals{SortExps{}, R}(Val:SortExps{}, inj{SortVals{}, SortExps{}}(From:SortVals{}))) [subsort{SortVals{}, SortExps{}}()]
            axiom{R} \equals{SortExps{}, R}(expsNil{}(), inj{SortVals{}, SortExps{}}(valsNil{}())) [symbol-overload{}(expsNil{}(), valsNil{}())]
            axiom{R} \equals{SortExps{}, R}(
                expsCons{}(inj{SortVal{}, SortExp{}}(K0:SortVal{}), inj{SortVals{}, SortExps{}}(K1:SortVals{})),
                inj{SortVals{}, SortExps{}}(valsCons{}(K0:SortVal{}, K1:SortVals{}))
            ) [symbol-overload{}(expsCons{}(), valsCons{}())]
        endmodule []";

    pub(crate) fn vals_overloads() -> Overloads {
        let mut backend = Backend::new(VALS, "MAIN", BackendOptions::default()).unwrap();
        let definition = backend.select_definition(None).unwrap();
        Overloads::new(definition.axioms())
    }

    fn normal(overloads: &Overloads, text: &str) -> String {
        overloads
            .normalize(&parse_pattern(text).unwrap())
            .to_string()
    }

    /// An `Exps` list of values is the `Vals` list the axioms equate with it, its injections
    /// composed; an `Exps` whose element is no `Val` keeps that cons, and only its tail is the
    /// `Vals` overload.
    #[test]
    fn a_term_rewrites_to_its_overload_only_where_the_arguments_are_the_overloads_sorts() {
        let overloads = vals_overloads();
        assert_eq!(
            normal(
                &overloads,
                r"expsCons{}(inj{SortInt{}, SortExp{}}(one{}()), expsNil{}())"
            ),
            parse_pattern(
                r"inj{SortVals{}, SortExps{}}(valsCons{}(inj{SortInt{}, SortVal{}}(one{}()), valsNil{}()))"
            )
            .unwrap()
            .to_string(),
        );
        assert_eq!(
            normal(&overloads, r"expsCons{}(tick{}(), expsNil{}())"),
            parse_pattern(r"expsCons{}(tick{}(), inj{SortVals{}, SortExps{}}(valsNil{}()))")
                .unwrap()
                .to_string(),
        );
    }

    /// A `\left-assoc` application is rewritten inside its arguments, never at its own symbol;
    /// without an overload axiom, a term is compared as it is, uncopied.
    #[test]
    fn an_associative_application_is_rewritten_inside_its_arguments_only() {
        let overloads = vals_overloads();
        assert_eq!(
            normal(
                &overloads,
                r"\left-assoc{}(expsCons{}(inj{SortInt{}, SortExp{}}(one{}()), expsNil{}()))"
            ),
            parse_pattern(
                r"\left-assoc{}(expsCons{}(inj{SortInt{}, SortExp{}}(one{}()), inj{SortVals{}, SortExps{}}(valsNil{}())))"
            )
            .unwrap()
            .to_string(),
        );
        let term = parse_pattern(r"expsCons{}(tick{}(), expsNil{}())").unwrap();
        assert!(matches!(
            Overloads::default().normalize(&term),
            std::borrow::Cow::Borrowed(_)
        ));
    }
}
