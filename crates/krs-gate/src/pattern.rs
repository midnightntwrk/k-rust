//! Structural KORE observation and collection normalization for gate expectations.

use k_rust::{
    definition::{
        Definition as FrontendDefinition, ProductionItem, Sentence as FrontendSentence,
        expand_configurations,
    },
    kast::{Sort as KastSort, identifier},
    kore::{
        ast::{Definition, Pattern, Sentence, Symbol},
        walk,
    },
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CollectionKind {
    List,
    Map,
    Set,
}

/// Definition-derived symbol and cell metadata for structural observations.
#[derive(Default)]
pub struct PatternContext {
    concat: BTreeMap<String, (CollectionKind, Symbol)>,
    units: BTreeSet<String>,
    cell_sorts: BTreeMap<String, KastSort>,
}

fn hook(attributes: &k_rust::kore::ast::Attributes) -> Option<&str> {
    attributes.0.iter().find_map(|attribute| {
        if let Pattern::Application { symbol, arguments } = attribute
            && symbol.name == "hook"
            && let [Pattern::String(value)] = arguments.as_slice()
        {
            value.as_utf8().ok()
        } else {
            None
        }
    })
}

impl PatternContext {
    /// Discover builtin collection hooks in compiled KORE.
    ///
    /// # Errors
    ///
    /// Returns an error if a collection concat has no unit of the same result sort.
    pub fn from_definition(definition: &Definition) -> Result<Self, String> {
        let mut result = Self::default();
        let mut concat_sorts = BTreeMap::new();
        let mut units_by_sort = BTreeMap::new();
        for module in &definition.modules {
            for sentence in &module.sentences {
                if let Sentence::SymbolDeclaration {
                    symbol,
                    result_sort,
                    attributes,
                    ..
                } = sentence
                {
                    let kind = match hook(attributes) {
                        Some("LIST.concat" | "LIST.unit") => Some(CollectionKind::List),
                        Some("MAP.concat" | "MAP.unit") => Some(CollectionKind::Map),
                        Some("SET.concat" | "SET.unit") => Some(CollectionKind::Set),
                        _ => None,
                    };
                    if let Some(kind) = kind {
                        match hook(attributes) {
                            Some("LIST.concat" | "MAP.concat" | "SET.concat") => {
                                concat_sorts
                                    .insert(symbol.name.clone(), (kind, result_sort.clone()));
                            }
                            Some("LIST.unit" | "MAP.unit" | "SET.unit") => {
                                units_by_sort.insert((kind, result_sort.clone()), symbol.clone());
                                result.units.insert(symbol.name.clone());
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        for (name, (kind, sort)) in concat_sorts {
            let unit = units_by_sort.get(&(kind, sort)).ok_or_else(|| {
                format!("collection concat `{name}` has no unit of the same result sort")
            })?;
            result.concat.insert(name, (kind, unit.clone()));
        }
        Ok(result)
    }

    /// Read single-content cell sorts from expanded frontend productions.
    ///
    /// # Errors
    ///
    /// Returns an error if frontend configuration expansion fails.
    pub fn with_frontend_cells(
        mut self,
        definition: &FrontendDefinition,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let expanded = expand_configurations(definition)?;
        for module in &expanded.modules {
            for sentence in &module.local_sentences {
                if let FrontendSentence::Production {
                    label: Some(label),
                    items,
                    ..
                } = &**sentence
                    && let Some(name) = label
                        .name
                        .strip_prefix('<')
                        .and_then(|name| name.strip_suffix('>'))
                {
                    let sorts = items
                        .iter()
                        .filter_map(|item| match item {
                            ProductionItem::NonTerminal { sort, .. } => Some(sort),
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    if let [sort] = sorts.as_slice() {
                        self.cell_sorts.insert(name.to_owned(), (*sort).clone());
                    }
                }
            }
        }
        Ok(self)
    }

    /// Return the declared content sort of a cell.
    #[must_use]
    pub fn cell_sort(&self, cell: &str) -> Option<&KastSort> {
        self.cell_sorts.get(cell)
    }

    fn flatten(&self, pattern: &Pattern, unit: &Symbol, output: &mut Vec<Pattern>) {
        if let Pattern::Application { symbol, arguments } = pattern {
            if symbol.name == unit.name && arguments.is_empty() {
                return;
            }
            if self
                .concat
                .get(&symbol.name)
                .is_some_and(|(_, concat_unit)| concat_unit == unit)
            {
                for argument in arguments {
                    self.flatten(argument, unit, output);
                }
                return;
            }
        }
        output.push(pattern.clone());
    }

    /// Normalize all nested collection applications through their declared hooks.
    #[must_use]
    pub fn normalize(&self, pattern: Pattern) -> Pattern {
        match &pattern {
            Pattern::Application { symbol, arguments } => {
                let arguments = arguments
                    .iter()
                    .cloned()
                    .map(|arg| self.normalize(arg))
                    .collect();
                let rebuilt = Pattern::Application {
                    symbol: symbol.clone(),
                    arguments,
                };
                if let Some((kind, unit)) = self.concat.get(&symbol.name) {
                    let mut elements = Vec::new();
                    self.flatten(&rebuilt, unit, &mut elements);
                    if *kind != CollectionKind::List {
                        elements.sort();
                    }
                    let mut iter = elements.into_iter();
                    if let Some(first) = iter.next() {
                        iter.fold(first, |left, right| Pattern::Application {
                            symbol: symbol.clone(),
                            arguments: vec![left, right],
                        })
                    } else {
                        Pattern::Application {
                            symbol: unit.clone(),
                            arguments: Vec::new(),
                        }
                    }
                } else {
                    rebuilt
                }
            }
            Pattern::AssociativeApplication {
                associativity,
                symbol,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .cloned()
                    .map(|arg| self.normalize(arg))
                    .collect::<Vec<_>>();
                if let Some((_, unit)) = self.concat.get(&symbol.name) {
                    let mut iter = arguments.into_iter();
                    let first = iter.next().unwrap_or_else(|| Pattern::Application {
                        symbol: unit.clone(),
                        arguments: Vec::new(),
                    });
                    self.normalize(iter.fold(first, |left, right| Pattern::Application {
                        symbol: symbol.clone(),
                        arguments: vec![left, right],
                    }))
                } else {
                    Pattern::AssociativeApplication {
                        associativity: *associativity,
                        symbol: symbol.clone(),
                        arguments,
                    }
                }
            }
            Pattern::And { sort, arguments } => Pattern::And {
                sort: sort.clone(),
                arguments: arguments
                    .iter()
                    .cloned()
                    .map(|arg| self.normalize(arg))
                    .collect(),
            },
            Pattern::Or { sort, arguments } => Pattern::Or {
                sort: sort.clone(),
                arguments: arguments
                    .iter()
                    .cloned()
                    .map(|arg| self.normalize(arg))
                    .collect(),
            },
            _ => self.normalize_unary(pattern),
        }
    }

    fn normalize_unary(&self, pattern: Pattern) -> Pattern {
        match &pattern {
            Pattern::Not { sort, argument } => Pattern::Not {
                sort: sort.clone(),
                argument: Box::new(self.normalize((**argument).clone())),
            },
            Pattern::Next { sort, argument } => Pattern::Next {
                sort: sort.clone(),
                argument: Box::new(self.normalize((**argument).clone())),
            },
            Pattern::Exists {
                sort,
                variable,
                body,
            } => Pattern::Exists {
                sort: sort.clone(),
                variable: variable.clone(),
                body: Box::new(self.normalize((**body).clone())),
            },
            Pattern::Forall {
                sort,
                variable,
                body,
            } => Pattern::Forall {
                sort: sort.clone(),
                variable: variable.clone(),
                body: Box::new(self.normalize((**body).clone())),
            },
            Pattern::Mu { variable, body } => Pattern::Mu {
                variable: variable.clone(),
                body: Box::new(self.normalize((**body).clone())),
            },
            Pattern::Nu { variable, body } => Pattern::Nu {
                variable: variable.clone(),
                body: Box::new(self.normalize((**body).clone())),
            },
            Pattern::Ceil {
                operand_sort,
                result_sort,
                argument,
            } => Pattern::Ceil {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                argument: Box::new(self.normalize((**argument).clone())),
            },
            Pattern::Floor {
                operand_sort,
                result_sort,
                argument,
            } => Pattern::Floor {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                argument: Box::new(self.normalize((**argument).clone())),
            },
            _ => self.normalize_binary(pattern),
        }
    }

    fn normalize_binary(&self, pattern: Pattern) -> Pattern {
        match &pattern {
            Pattern::Implies { sort, left, right } => Pattern::Implies {
                sort: sort.clone(),
                left: Box::new(self.normalize((**left).clone())),
                right: Box::new(self.normalize((**right).clone())),
            },
            Pattern::Iff { sort, left, right } => Pattern::Iff {
                sort: sort.clone(),
                left: Box::new(self.normalize((**left).clone())),
                right: Box::new(self.normalize((**right).clone())),
            },
            Pattern::Rewrites { sort, left, right } => Pattern::Rewrites {
                sort: sort.clone(),
                left: Box::new(self.normalize((**left).clone())),
                right: Box::new(self.normalize((**right).clone())),
            },
            Pattern::Equals {
                operand_sort,
                result_sort,
                left,
                right,
            } => Pattern::Equals {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: Box::new(self.normalize((**left).clone())),
                right: Box::new(self.normalize((**right).clone())),
            },
            Pattern::In {
                operand_sort,
                result_sort,
                left,
                right,
            } => Pattern::In {
                operand_sort: operand_sort.clone(),
                result_sort: result_sort.clone(),
                left: Box::new(self.normalize((**left).clone())),
                right: Box::new(self.normalize((**right).clone())),
            },
            _ => pattern,
        }
    }

    /// Count the elements of a collection term, if it is collection sorted.
    #[must_use]
    pub fn collection_size(&self, pattern: &Pattern) -> Option<usize> {
        if let Pattern::Application { symbol, arguments } = pattern {
            if self.units.contains(&symbol.name) && arguments.is_empty() {
                return Some(0);
            }
            if self.concat.contains_key(&symbol.name) {
                return Some(
                    arguments
                        .iter()
                        .map(|arg| self.collection_size(arg).unwrap_or(1))
                        .sum(),
                );
            }
            if symbol.name == "inj" && arguments.len() == 1 {
                return self.collection_size(&arguments[0]);
            }
        }
        None
    }

    /// Count elements when a cell's declared sort is a builtin collection.
    #[must_use]
    pub fn cell_collection_size(&self, cell: &str, pattern: &Pattern) -> Option<usize> {
        let sort = self.cell_sorts.get(cell)?;
        if matches!(sort.name.as_str(), "List" | "Map" | "Set") {
            Some(self.collection_size(pattern).unwrap_or(1))
        } else {
            None
        }
    }
}

/// Find the unique structurally nested cell and return its content.
///
/// # Errors
///
/// Returns an error if the cell is absent or occurs more than once.
pub fn cell<'a>(state: &'a Pattern, name: &str) -> Result<&'a Pattern, String> {
    let label = identifier::encode_label(&format!("<{name}>"));
    let mut matches = Vec::new();
    let mut pending = vec![state];
    while let Some(node) = pending.pop() {
        if let Pattern::Application { symbol, arguments }
        | Pattern::AssociativeApplication {
            symbol, arguments, ..
        } = node
            && symbol.name == label
        {
            if let [content] = arguments.as_slice() {
                matches.push(content);
            } else {
                return Err(format!("<{name}> cell is malformed"));
            }
        }
        pending.extend(walk::children(node));
    }
    if matches.len() == 1 {
        Ok(matches[0])
    } else {
        Err(format!("state contains {} <{name}> cells", matches.len()))
    }
}

#[cfg(test)]
mod tests {
    use super::{PatternContext, cell};
    use k_rust::kore::{
        ast::{Associativity, Pattern, Symbol},
        parser::{parse_definition, parse_pattern},
    };

    #[test]
    fn normalizes_nested_collection_axioms() {
        let definition = parse_definition("[] module M hooked-symbol lc{}(SortList{},SortList{}):SortList{} [hook{}(\"LIST.concat\")] hooked-symbol lu{}():SortList{} [hook{}(\"LIST.unit\")] hooked-symbol mc{}(SortMap{},SortMap{}):SortMap{} [hook{}(\"MAP.concat\")] hooked-symbol mu{}():SortMap{} [hook{}(\"MAP.unit\")] hooked-symbol sc{}(SortSet{},SortSet{}):SortSet{} [hook{}(\"SET.concat\")] hooked-symbol su{}():SortSet{} [hook{}(\"SET.unit\")] endmodule []").unwrap();
        let context = PatternContext::from_definition(&definition).unwrap();
        let left = parse_pattern("lc{}(a{}(),lc{}(lu{}(),b{}()))").unwrap();
        let right = parse_pattern("lc{}(a{}(),b{}())").unwrap();
        assert_eq!(context.normalize(left), context.normalize(right.clone()));
        let reversed = parse_pattern("lc{}(b{}(),a{}())").unwrap();
        assert_ne!(
            context.normalize(reversed),
            context.normalize(right.clone())
        );
        let map = parse_pattern("mc{}(x{}(),mc{}(mu{}(),y{}()))").unwrap();
        let swapped = parse_pattern("mc{}(y{}(),x{}())").unwrap();
        assert_eq!(context.normalize(map), context.normalize(swapped));
        let nested =
            parse_pattern("mc{}(x{}(sc{}(q{}(),su{}())),y{}(lc{}(a{}(),lu{}())))").unwrap();
        let nested_swapped = parse_pattern("mc{}(y{}(a{}()),x{}(q{}()))").unwrap();
        assert_eq!(context.normalize(nested), context.normalize(nested_swapped));
        let set = parse_pattern("sc{}(q{}(),sc{}(su{}(),r{}()))").unwrap();
        let set_swapped = parse_pattern("sc{}(r{}(),q{}())").unwrap();
        assert_eq!(context.normalize(set), context.normalize(set_swapped));
        let wrapped = parse_pattern("\\not{SortMap{}}(mc{}(x{}(),mu{}()))").unwrap();
        let wrapped_simple = parse_pattern("\\not{SortMap{}}(x{}())").unwrap();
        assert_eq!(
            context.normalize(wrapped),
            context.normalize(wrapped_simple)
        );
        assert_eq!(context.collection_size(&context.normalize(right)), Some(2));
    }

    #[test]
    fn collection_units_are_paired_by_result_sort() {
        let definition = parse_definition(concat!(
            "[] module M ",
            "hooked-symbol mc{}(SortMap{},SortMap{}):SortMap{} [hook{}(\"MAP.concat\")] ",
            "hooked-symbol mu{}():SortMap{} [hook{}(\"MAP.unit\")] ",
            "hooked-symbol ac{}(SortAccountCellMap{},SortAccountCellMap{}):SortAccountCellMap{} [hook{}(\"MAP.concat\")] ",
            "hooked-symbol au{}():SortAccountCellMap{} [hook{}(\"MAP.unit\")] ",
            "endmodule []",
        ))
        .unwrap();
        let context = PatternContext::from_definition(&definition).unwrap();
        let item = parse_pattern("x{}()").unwrap();
        for (concat, unit) in [("mc", "mu"), ("ac", "au")] {
            let unit_pattern = parse_pattern(&format!("{unit}{{}}()")).unwrap();
            let nonempty = parse_pattern(&format!("{concat}{{}}({unit}{{}}(),x{{}}())")).unwrap();
            assert_eq!(context.normalize(nonempty), item);
            let empty = parse_pattern(&format!("{concat}{{}}({unit}{{}}(),{unit}{{}}())")).unwrap();
            assert_eq!(context.normalize(empty), unit_pattern);
            let associative_empty = Pattern::AssociativeApplication {
                associativity: Associativity::Left,
                symbol: Symbol {
                    name: concat.to_owned(),
                    sort_parameters: Vec::new(),
                },
                arguments: Vec::new(),
            };
            assert_eq!(context.normalize(associative_empty), unit_pattern);
            assert_eq!(context.collection_size(&unit_pattern), Some(0));
        }
    }

    #[test]
    fn collection_concat_requires_a_unit_of_its_result_sort() {
        let definition = parse_definition(concat!(
            "[] module M ",
            "hooked-symbol mc{}(SortMap{},SortMap{}):SortMap{} [hook{}(\"MAP.concat\")] ",
            "hooked-symbol au{}():SortAccountCellMap{} [hook{}(\"MAP.unit\")] ",
            "endmodule []",
        ))
        .unwrap();
        let error = PatternContext::from_definition(&definition).err().unwrap();
        assert_eq!(
            error,
            "collection concat `mc` has no unit of the same result sort"
        );
    }

    #[test]
    fn unique_cell_is_required() {
        let one = parse_pattern("Lbl'-LT-'k'-GT-'{}(a{}())").unwrap();
        assert!(cell(&one, "k").is_ok());
        assert!(cell(&one, "locals").is_err());
        let two =
            parse_pattern("pair{}(Lbl'-LT-'k'-GT-'{}(a{}()),Lbl'-LT-'k'-GT-'{}(b{}()))").unwrap();
        assert!(cell(&two, "k").is_err());
    }
}
