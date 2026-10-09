//! The print data `kprint` reads from `syntaxDefinition.kore` and `macros.kore` (`get_print_data`).

use std::collections::{BTreeMap, BTreeSet};

use k_rust::kore::ast::{Attributes, Pattern, Sentence, Sort};

use crate::node::{Declaration, Node, from_pattern, instantiate};

/// The built-in formats `kprint` knows before it reads any declaration.
const BUILTIN_FORMATS: &[(&str, &str, &str)] = &[
    ("kseq", "%1 ~> %2", "010"),
    ("append", "%1 ~> %2", "010"),
    ("dotk", ".K", "1"),
    ("inj", "%1", "0"),
    ("\\bottom", "#Bottom", "1"),
    ("\\top", "#Top", "1"),
    ("\\not", "#Not ( %1 )", "101"),
    ("\\ceil", "#Ceil ( %1 )", "101"),
    ("\\floor", "#Floor ( %1 )", "101"),
    ("\\equals", "{%i%n%1%d%n#Equals%i%n%2%d%n}", "10101"),
    ("\\and", "%i%1%d%n#And%n%i%2%d", "010"),
    ("\\or", "%i%1%d%n#Or%n%i%2%d", "010"),
    ("\\implies", "%i%1%d%n#Implies%n%i%2%d", "010"),
    ("\\exists", "#Exists %1 . %2", "1010"),
    ("\\forall", "#Forall %1 . %2", "1010"),
    ("\\rewrites", "%1 => %2", "010"),
    ("weakAlwaysFinally", "#wAF ( %1 )", "101"),
    ("weakExistsFinally", "#wEF ( %1 )", "101"),
    ("allPathGlobally", "#AG ( %1 )", "101"),
    ("bracket", "( %1 )", "101"),
];

/// The built-in priorities: `(outer, inner)` pairs where `inner` may not appear directly under `outer`.
const BUILTIN_PRIORITIES: &[(&str, &[&str])] = &[
    ("\\implies", &["\\exists", "\\forall"]),
    ("\\or", &["\\exists", "\\forall", "\\implies"]),
    ("\\and", &["\\exists", "\\forall", "\\implies", "\\or"]),
    (
        "\\equals",
        &["\\exists", "\\forall", "\\implies", "\\or", "\\and"],
    ),
    (
        "\\floor",
        &[
            "\\exists",
            "\\forall",
            "\\implies",
            "\\or",
            "\\and",
            "\\equals",
        ],
    ),
    (
        "\\ceil",
        &[
            "\\exists",
            "\\forall",
            "\\implies",
            "\\or",
            "\\and",
            "\\equals",
        ],
    ),
    (
        "\\not",
        &[
            "\\exists",
            "\\forall",
            "\\implies",
            "\\or",
            "\\and",
            "\\equals",
        ],
    ),
    (
        "\\bottom",
        &[
            "\\exists",
            "\\forall",
            "\\implies",
            "\\or",
            "\\and",
            "\\equals",
        ],
    ),
    (
        "\\top",
        &[
            "\\exists",
            "\\forall",
            "\\implies",
            "\\or",
            "\\and",
            "\\equals",
        ],
    ),
];

/// One macro, alias, or recursive variant from `macros.kore`.
#[derive(Clone, Debug)]
pub(crate) struct Macro {
    pub left: Node,
    pub right: Node,
    /// `macro` or `macro-rec`: never reversed.
    pub one_way: bool,
    /// `macro-rec` or `alias-rec`: may apply repeatedly on one path.
    pub recursive: bool,
}

/// Everything `pretty_print_data` holds, plus the symbol declarations and overloads.
#[derive(Clone, Debug, Default)]
pub(crate) struct PrintData {
    pub format: BTreeMap<String, String>,
    pub colors: BTreeMap<String, Vec<String>>,
    pub terminals: BTreeMap<String, String>,
    pub priorities: BTreeMap<String, BTreeSet<String>>,
    pub left_assoc: BTreeMap<String, BTreeSet<String>>,
    pub right_assoc: BTreeMap<String, BTreeSet<String>>,
    /// Sort name (`SortString`) to hook (`STRING.String`).
    pub hooks: BTreeMap<String, String>,
    /// Bracket symbols by declared result sort, in declaration order.
    pub brackets: Vec<(Sort, Vec<BracketSymbol>)>,
    pub assoc: BTreeSet<String>,
    pub comm: BTreeSet<String>,
    /// The transitive strict supersorts of each sort.
    pub subsorts: BTreeMap<Sort, BTreeSet<Sort>>,
    /// The transitive overloads of each symbol: the symbols it is overloaded by.
    pub overloads: BTreeMap<String, BTreeSet<String>>,
    pub declarations: BTreeMap<String, Declaration>,
}

/// A bracket production's symbol and declared argument sort.
#[derive(Clone, Debug)]
pub(crate) struct BracketSymbol {
    pub name: String,
    pub argument: Option<Sort>,
}

/// The name of an attribute pattern, without the `'Kywd'` escape K writes for KORE keywords.
fn attribute_name(attribute: &Pattern) -> Option<&str> {
    match attribute {
        Pattern::Application { symbol, .. } => {
            Some(symbol.name.strip_suffix("'Kywd'").unwrap_or(&symbol.name))
        }
        _ => None,
    }
}

fn attribute<'a>(attributes: &'a Attributes, name: &str) -> Option<&'a Pattern> {
    attributes
        .0
        .iter()
        .find(|attribute| attribute_name(attribute) == Some(name))
}

fn has(attributes: &Attributes, name: &str) -> bool {
    attribute(attributes, name).is_some()
}

fn attribute_arguments<'a>(attributes: &'a Attributes, name: &str) -> &'a [Pattern] {
    match attribute(attributes, name) {
        Some(Pattern::Application { arguments, .. }) => arguments,
        _ => &[],
    }
}

/// The string argument of `name{}("...")`.
fn attribute_string(attributes: &Attributes, name: &str) -> Option<String> {
    match attribute_arguments(attributes, name) {
        [Pattern::String(value)] => Some(String::from_utf8_lossy(value.as_bytes()).into_owned()),
        _ => None,
    }
}

/// The symbol names of `name{}(Lbl1{}(), Lbl2{}())` (`read_multimap`).
fn attribute_symbols(attributes: &Attributes, name: &str) -> BTreeSet<String> {
    attribute_arguments(attributes, name)
        .iter()
        .filter_map(|argument| match argument {
            Pattern::Application { symbol, .. } => Some(symbol.name.clone()),
            _ => None,
        })
        .collect()
}

/// `kprint`'s `trim`.
fn trim(text: &str) -> &str {
    text.trim_matches([' ', '\n', '\r', '\t', '\x0c', '\x0b'])
}

fn transitive_closure<T: Ord + Clone>(relation: &mut BTreeMap<T, BTreeSet<T>>) {
    loop {
        let mut dirty = false;
        let keys = relation.keys().cloned().collect::<Vec<_>>();
        for key in keys {
            let successors = relation[&key].iter().cloned().collect::<Vec<_>>();
            let mut added = BTreeSet::new();
            for successor in successors {
                if let Some(next) = relation.get(&successor) {
                    added.extend(next.iter().cloned());
                }
            }
            let entry = relation.get_mut(&key).expect("key is present");
            for value in added {
                dirty |= entry.insert(value);
            }
        }
        if !dirty {
            return;
        }
    }
}

impl PrintData {
    /// Read the print data from the sentences of `syntaxDefinition.kore`.
    pub fn new(sentences: &[&Sentence]) -> Self {
        let mut data = Self::default();
        for (name, format, terminals) in BUILTIN_FORMATS {
            data.format.insert((*name).to_owned(), (*format).to_owned());
            data.terminals
                .insert((*name).to_owned(), (*terminals).to_owned());
        }
        data.assoc
            .extend(["kseq", "\\and", "\\or"].map(str::to_owned));
        data.comm.extend(["\\and", "\\or"].map(str::to_owned));
        for (outer, inner) in [
            ("kseq", "kseq"),
            ("append", "append"),
            ("\\and", "\\and"),
            ("\\or", "\\or"),
            ("\\rewrites", "\\rewrites"),
        ] {
            data.left_assoc
                .entry(outer.to_owned())
                .or_default()
                .insert(inner.to_owned());
        }
        data.right_assoc
            .entry("\\rewrites".to_owned())
            .or_default()
            .insert("\\rewrites".to_owned());
        for (outer, inner) in BUILTIN_PRIORITIES {
            data.priorities
                .entry((*outer).to_owned())
                .or_default()
                .extend(inner.iter().map(|name| (*name).to_owned()));
        }
        for sentence in sentences {
            match sentence {
                Sentence::SymbolDeclaration {
                    symbol,
                    argument_sorts,
                    result_sort,
                    attributes,
                    ..
                } => data.symbol(
                    &symbol.name,
                    symbol
                        .sort_parameters
                        .iter()
                        .filter_map(|sort| match sort {
                            Sort::Variable(name) => Some(name.clone()),
                            Sort::Application { .. } => None,
                        })
                        .collect(),
                    argument_sorts,
                    result_sort,
                    attributes,
                ),
                Sentence::SortDeclaration {
                    name, attributes, ..
                } => {
                    if let Some(hook) = attribute_string(attributes, "hook") {
                        data.hooks.insert(name.clone(), hook);
                    }
                }
                Sentence::Axiom { attributes, .. } => data.axiom(attributes),
                _ => {}
            }
        }
        transitive_closure(&mut data.subsorts);
        transitive_closure(&mut data.overloads);
        data
    }

    fn symbol(
        &mut self,
        name: &str,
        parameters: Vec<String>,
        argument_sorts: &[Sort],
        result_sort: &Sort,
        attributes: &Attributes,
    ) {
        self.declarations.insert(
            name.to_owned(),
            Declaration {
                parameters,
                arguments: argument_sorts.to_vec(),
                result: result_sort.clone(),
            },
        );
        let Some(format) = attribute_string(attributes, "format") else {
            return;
        };
        self.format.insert(name.to_owned(), format);
        self.terminals.insert(
            name.to_owned(),
            attribute_string(attributes, "terminals").unwrap_or_default(),
        );
        if has(attributes, "assoc") {
            self.assoc.insert(name.to_owned());
        }
        if has(attributes, "comm") {
            self.comm.insert(name.to_owned());
        }
        if let Some(colors) = attribute_string(attributes, "colors") {
            self.colors.insert(
                name.to_owned(),
                colors
                    .split(',')
                    .map(|color| trim(color).to_owned())
                    .collect(),
            );
        }
        if has(attributes, "bracket") {
            let bracket = BracketSymbol {
                name: name.to_owned(),
                argument: argument_sorts.first().cloned(),
            };
            match self
                .brackets
                .iter_mut()
                .find(|(sort, _)| sort == result_sort)
            {
                Some((_, symbols)) => symbols.push(bracket),
                None => self.brackets.push((result_sort.clone(), vec![bracket])),
            }
        }
        for (key, map) in [
            ("left", &mut self.left_assoc),
            ("right", &mut self.right_assoc),
            ("priorities", &mut self.priorities),
        ] {
            if has(attributes, key) {
                map.entry(name.to_owned())
                    .or_default()
                    .extend(attribute_symbols(attributes, key));
            }
        }
    }

    fn axiom(&mut self, attributes: &Attributes) {
        if let Some(Pattern::Application { symbol, .. }) = attribute(attributes, "subsort")
            && let [inner, outer] = symbol.sort_parameters.as_slice()
        {
            self.subsorts
                .entry(inner.clone())
                .or_default()
                .insert(outer.clone());
        }
        if let [
            Pattern::Application { symbol: outer, .. },
            Pattern::Application { symbol: inner, .. },
        ] = attribute_arguments(attributes, "symbol-overload")
        {
            self.overloads
                .entry(inner.name.clone())
                .or_default()
                .insert(outer.name.clone());
        }
    }

    /// `less_than_eq`: `left` is `right` or one of its subsorts.
    pub fn less_than_eq(&self, left: &Sort, right: &Sort) -> bool {
        left == right
            || self
                .subsorts
                .get(left)
                .is_some_and(|supersorts| supersorts.contains(right))
    }

    /// Read the macro axioms `\equals(lhs, rhs)` of `macros.kore`, instantiated like the term.
    pub fn macros(&self, sentences: &[&Sentence]) -> Vec<Macro> {
        sentences
            .iter()
            .filter_map(|sentence| {
                let Sentence::Axiom {
                    pattern,
                    attributes,
                    ..
                } = sentence
                else {
                    return None;
                };
                let Pattern::Equals { left, right, .. } = &**pattern else {
                    return None;
                };
                let mut left = from_pattern(left);
                let mut right = from_pattern(right);
                instantiate(&mut left, &self.declarations);
                instantiate(&mut right, &self.declarations);
                Some(Macro {
                    left,
                    right,
                    one_way: has(attributes, "macro") || has(attributes, "macro-rec"),
                    recursive: has(attributes, "macro-rec") || has(attributes, "alias-rec"),
                })
            })
            .collect()
    }
}
