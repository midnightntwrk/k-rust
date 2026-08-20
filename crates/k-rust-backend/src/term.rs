//! Immutable backend terms with cached synthetic attributes.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, hash_map::DefaultHasher},
    hash::{Hash, Hasher},
    sync::Arc,
};

pub type Name = Arc<str>;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sort {
    Application { name: Name, arguments: Vec<Sort> },
    Variable(Name),
}

impl Sort {
    pub fn application(name: impl Into<Name>, arguments: Vec<Self>) -> Self {
        Self::Application {
            name: name.into(),
            arguments,
        }
    }

    pub fn simple(name: impl Into<Name>) -> Self {
        Self::application(name, Vec::new())
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Variable {
    pub sort: Sort,
    pub name: Name,
}

impl Variable {
    pub fn new(name: impl Into<Name>, sort: Sort) -> Self {
        Self {
            sort,
            name: name.into(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum FunctionType {
    Partial,
    Total,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum SymbolType {
    Constructor,
    Function(FunctionType),
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SymbolAttributes {
    pub symbol_type: SymbolType,
    pub associative: bool,
    pub idempotent: bool,
    pub macro_or_alias: bool,
    pub has_evaluators: bool,
    pub hook: Option<Name>,
}

impl SymbolAttributes {
    pub fn constructor() -> Self {
        Self {
            symbol_type: SymbolType::Constructor,
            associative: false,
            idempotent: false,
            macro_or_alias: false,
            has_evaluators: true,
            hook: None,
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Symbol {
    pub name: Name,
    pub sort_variables: Vec<Name>,
    pub argument_sorts: Vec<Sort>,
    pub result_sort: Sort,
    pub attributes: SymbolAttributes,
}

impl Symbol {
    pub fn constructor(
        name: impl Into<Name>,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
    ) -> Self {
        Self {
            name: name.into(),
            sort_variables: Vec::new(),
            argument_sorts,
            result_sort,
            attributes: SymbolAttributes::constructor(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CollectionSymbols {
    pub unit: Name,
    pub element: Name,
    pub concat: Name,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MapDefinition {
    pub symbols: CollectionSymbols,
    pub key_sort: Name,
    pub value_sort: Name,
    pub map_sort: Name,
}

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ListDefinition {
    pub symbols: CollectionSymbols,
    pub element_sort: Name,
    pub list_sort: Name,
}

pub type SetDefinition = ListDefinition;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum TermKind {
    And(Term, Term),
    Application {
        symbol: Arc<Symbol>,
        sort_arguments: Vec<Sort>,
        arguments: Vec<Term>,
    },
    DomainValue {
        sort: Sort,
        value: Arc<str>,
    },
    Variable(Variable),
    Injection {
        source: Sort,
        target: Sort,
        term: Term,
    },
    Map {
        definition: Arc<MapDefinition>,
        entries: Vec<(Term, Term)>,
        rest: Option<Term>,
    },
    List {
        definition: Arc<ListDefinition>,
        heads: Vec<Term>,
        rest: Option<(Term, Vec<Term>)>,
    },
    Set {
        definition: Arc<SetDefinition>,
        elements: Vec<Term>,
        rest: Option<Term>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermAttributes {
    pub variables: BTreeSet<Variable>,
    pub evaluated: bool,
    pub constructor_like: bool,
    pub can_be_evaluated: bool,
    hash: u64,
}

impl Default for TermAttributes {
    fn default() -> Self {
        Self {
            variables: BTreeSet::new(),
            evaluated: true,
            constructor_like: false,
            can_be_evaluated: true,
            hash: 0,
        }
    }
}

#[derive(Debug)]
struct TermData {
    attributes: TermAttributes,
    kind: TermKind,
}

#[derive(Clone, Debug)]
pub struct Term(Arc<TermData>);

impl Term {
    pub fn and(left: Self, right: Self) -> Self {
        let mut attributes = combine_attributes([&left, &right]);
        attributes.constructor_like = false;
        Self::new(TermKind::And(left, right), attributes)
    }

    pub fn application(
        symbol: Arc<Symbol>,
        sort_arguments: Vec<Sort>,
        arguments: Vec<Self>,
    ) -> Self {
        if symbol.name.as_ref() == "inj"
            && let ([source, target], [argument]) =
                (sort_arguments.as_slice(), arguments.as_slice())
        {
            return Self::injection(source.clone(), target.clone(), argument.clone());
        }

        let mut attributes = combine_attributes(arguments.iter());
        let constructor = symbol.attributes.symbol_type == SymbolType::Constructor;
        attributes.evaluated = constructor && attributes.evaluated;
        attributes.constructor_like = constructor && attributes.constructor_like;
        attributes.can_be_evaluated =
            symbol.attributes.has_evaluators && attributes.can_be_evaluated;
        Self::new(
            TermKind::Application {
                symbol,
                sort_arguments,
                arguments,
            },
            attributes,
        )
    }

    pub fn domain_value(sort: Sort, value: impl Into<Arc<str>>) -> Self {
        let attributes = TermAttributes {
            constructor_like: true,
            ..TermAttributes::default()
        };
        Self::new(
            TermKind::DomainValue {
                sort,
                value: value.into(),
            },
            attributes,
        )
    }

    pub fn variable(variable: Variable) -> Self {
        let attributes = TermAttributes {
            variables: BTreeSet::from([variable.clone()]),
            ..TermAttributes::default()
        };
        Self::new(TermKind::Variable(variable), attributes)
    }

    pub fn injection(source: Sort, target: Sort, term: Self) -> Self {
        if let TermKind::Injection {
            source: inner_source,
            target: inner_target,
            term: inner,
        } = term.kind()
            && &source == inner_target
        {
            return Self::injection(inner_source.clone(), target, inner.clone());
        }
        Self::new(
            TermKind::Injection {
                source,
                target,
                term: term.clone(),
            },
            term.attributes().clone(),
        )
    }

    pub fn map(
        definition: Arc<MapDefinition>,
        mut entries: Vec<(Self, Self)>,
        rest: Option<Self>,
    ) -> Self {
        let (nested_entries, rest) = match rest {
            Some(rest) => match rest.kind() {
                TermKind::Map {
                    definition: nested,
                    entries,
                    rest,
                } if nested == &definition => (entries.clone(), rest.clone()),
                _ => (Vec::new(), Some(rest)),
            },
            None => (Vec::new(), None),
        };
        entries.extend(nested_entries);
        entries.sort();
        entries.dedup();
        if entries.is_empty()
            && let Some(rest) = rest
        {
            return rest;
        }
        let attributes = combine_attributes(
            entries
                .iter()
                .flat_map(|(key, value)| [key, value])
                .chain(rest.iter()),
        );
        Self::new(
            TermKind::Map {
                definition,
                entries,
                rest,
            },
            attributes,
        )
    }

    pub fn list(
        definition: Arc<ListDefinition>,
        mut heads: Vec<Self>,
        rest: Option<(Self, Vec<Self>)>,
    ) -> Self {
        let rest = match rest {
            Some((middle, tails)) => match middle.kind() {
                TermKind::List {
                    definition: nested,
                    heads: nested_heads,
                    rest: nested_rest,
                } if nested == &definition => {
                    heads.extend(nested_heads.iter().cloned());
                    match nested_rest {
                        Some((nested_middle, nested_tails)) => {
                            let mut combined_tails = nested_tails.clone();
                            combined_tails.extend(tails);
                            Some((nested_middle.clone(), combined_tails))
                        }
                        None => {
                            heads.extend(tails);
                            None
                        }
                    }
                }
                _ => Some((middle, tails)),
            },
            None => None,
        };
        if heads.is_empty()
            && let Some((middle, tails)) = &rest
            && tails.is_empty()
        {
            return middle.clone();
        }
        let attributes = combine_attributes(
            heads.iter().chain(
                rest.iter()
                    .flat_map(|(middle, tails)| std::iter::once(middle).chain(tails)),
            ),
        );
        Self::new(
            TermKind::List {
                definition,
                heads,
                rest,
            },
            attributes,
        )
    }

    pub fn set(
        definition: Arc<SetDefinition>,
        mut elements: Vec<Self>,
        rest: Option<Self>,
    ) -> Self {
        let (nested_elements, rest) = match rest {
            Some(rest) => match rest.kind() {
                TermKind::Set {
                    definition: nested,
                    elements,
                    rest,
                } if nested == &definition => (elements.clone(), rest.clone()),
                _ => (Vec::new(), Some(rest)),
            },
            None => (Vec::new(), None),
        };
        elements.extend(nested_elements);
        elements.sort();
        elements.dedup();
        if elements.is_empty()
            && let Some(rest) = rest
        {
            return rest;
        }
        let attributes = combine_attributes(elements.iter().chain(rest.iter()));
        Self::new(
            TermKind::Set {
                definition,
                elements,
                rest,
            },
            attributes,
        )
    }

    pub fn kind(&self) -> &TermKind {
        &self.0.kind
    }

    pub fn attributes(&self) -> &TermAttributes {
        &self.0.attributes
    }

    pub fn sort(&self) -> Sort {
        match self.kind() {
            TermKind::And(_, right) => right.sort(),
            TermKind::Application {
                symbol,
                sort_arguments,
                ..
            } => {
                let substitution = symbol
                    .sort_variables
                    .iter()
                    .cloned()
                    .zip(sort_arguments.iter().cloned())
                    .collect::<BTreeMap<_, _>>();
                substitute_sort(&symbol.result_sort, &substitution)
            }
            TermKind::DomainValue { sort, .. } | TermKind::Variable(Variable { sort, .. }) => {
                sort.clone()
            }
            TermKind::Injection { target, .. } => target.clone(),
            TermKind::Map { definition, .. } => Sort::simple(definition.map_sort.clone()),
            TermKind::List { definition, .. } | TermKind::Set { definition, .. } => {
                Sort::simple(definition.list_sort.clone())
            }
        }
    }

    fn new(kind: TermKind, mut attributes: TermAttributes) -> Self {
        attributes.hash = calculate_hash(&kind);
        Self(Arc::new(TermData { attributes, kind }))
    }
}

fn substitute_sort(sort: &Sort, substitution: &BTreeMap<Name, Sort>) -> Sort {
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

fn combine_attributes<'a>(terms: impl IntoIterator<Item = &'a Term>) -> TermAttributes {
    let mut terms = terms.into_iter();
    let Some(first) = terms.next() else {
        return TermAttributes::default();
    };
    let mut combined = first.attributes().clone();
    for term in terms {
        let attributes = term.attributes();
        combined
            .variables
            .extend(attributes.variables.iter().cloned());
        combined.evaluated &= attributes.evaluated;
        combined.constructor_like &= attributes.constructor_like;
        combined.can_be_evaluated &= attributes.can_be_evaluated;
    }
    combined.hash = 0;
    combined
}

fn calculate_hash(kind: &TermKind) -> u64 {
    let mut hasher = DefaultHasher::new();
    kind.hash(&mut hasher);
    hasher.finish()
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
            || (self.0.attributes.hash == other.0.attributes.hash && self.0.kind == other.0.kind)
    }
}

impl Eq for Term {}

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.kind.cmp(&other.0.kind)
    }
}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.attributes.hash);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sort() -> Sort {
        Sort::simple("SomeSort")
    }

    fn constructor() -> Arc<Symbol> {
        Arc::new(Symbol::constructor("con1", vec![sort()], sort()))
    }

    fn collection_symbols() -> CollectionSymbols {
        CollectionSymbols {
            unit: "unit".into(),
            element: "element".into(),
            concat: "concat".into(),
        }
    }

    #[test]
    fn caches_free_variables_and_constructor_attributes() {
        let variable = Variable::new("X", sort());
        let term = Term::application(
            constructor(),
            Vec::new(),
            vec![Term::variable(variable.clone())],
        );
        assert_eq!(term.attributes().variables, BTreeSet::from([variable]));
        assert!(!term.attributes().constructor_like);

        let concrete = Term::application(
            constructor(),
            Vec::new(),
            vec![Term::domain_value(sort(), "value")],
        );
        assert!(concrete.attributes().constructor_like);
        assert!(concrete.attributes().evaluated);
    }

    #[test]
    fn collapses_nested_injections() {
        let a = Sort::simple("A");
        let b = Sort::simple("B");
        let c = Sort::simple("C");
        let value = Term::domain_value(a.clone(), "value");
        let nested = Term::injection(
            b.clone(),
            c.clone(),
            Term::injection(a.clone(), b, value.clone()),
        );
        assert_eq!(nested, Term::injection(a, c, value));
    }

    #[test]
    fn clones_share_immutable_storage() {
        let term = Term::domain_value(sort(), "value");
        assert!(Arc::ptr_eq(&term.0, &term.clone().0));
    }

    #[test]
    fn canonicalizes_internal_collections() {
        let one = Term::domain_value(sort(), "1");
        let two = Term::domain_value(sort(), "2");
        let map_definition = Arc::new(MapDefinition {
            symbols: collection_symbols(),
            key_sort: "Key".into(),
            value_sort: "Value".into(),
            map_sort: "Map".into(),
        });
        let nested_map = Term::map(
            map_definition.clone(),
            vec![(two.clone(), one.clone())],
            None,
        );
        let map = Term::map(
            map_definition,
            vec![(one.clone(), two.clone()), (one.clone(), two.clone())],
            Some(nested_map),
        );
        let TermKind::Map { entries, .. } = map.kind() else {
            panic!("expected an internal map")
        };
        assert_eq!(entries.len(), 2);
        assert!(entries.windows(2).all(|pair| pair[0] < pair[1]));

        let set_definition = Arc::new(SetDefinition {
            symbols: collection_symbols(),
            element_sort: "Element".into(),
            list_sort: "Set".into(),
        });
        let set = Term::set(
            set_definition,
            vec![two.clone(), one.clone(), one.clone()],
            None,
        );
        let TermKind::Set { elements, .. } = set.kind() else {
            panic!("expected an internal set")
        };
        assert_eq!(elements, &[one, two]);
    }
}
